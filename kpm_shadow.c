#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/kprobes.h>
#include <linux/sched.h>
#include <linux/sched/mm.h>
#include <linux/mm.h>
#include <linux/uaccess.h>
#include <linux/highmem.h>
#include <asm/pgtable.h>
#include <asm/tlbflush.h>
#include <linux/pgtable.h>

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Reverse Engineering Expert");
MODULE_DESCRIPTION("Android WuWa - PTE Swap Shadow Page Engine");

#define PR_WXSHADOW_PATCH   0x57580006
#define PR_WXSHADOW_RELEASE 0x57580008

/* 【新增】接收来自装载脚本的动态基址投喂 */
static unsigned long p_prctl_addr = 0;
module_param(p_prctl_addr, ulong, 0400);

#ifndef pte_pgprot
static inline pgprot_t my_pte_pgprot(pte_t pte) {
    return __pgprot(pte_val(pte) ^ pte_val(pfn_pte(pte_pfn(pte), __pgprot(0))));
}
#define pte_pgprot my_pte_pgprot
#endif

static void force_flush_tlb_icache(void)
{
    asm volatile(
        "dsb ishst\n"        
        "tlbi vmalle1is\n"   
        "dsb ish\n"          
        "isb\n"              
        "ic ialluis\n"       
        "dsb ish\n"
        "isb\n"
        : : : "memory");
}

static int apply_shadow_pte(pid_t pid, unsigned long vaddr, void __user *patch_buf, size_t patch_len)
{
    struct task_struct *task;
    struct mm_struct *mm;
    pgd_t *pgd; p4d_t *p4d; pud_t *pud; pmd_t *pmd; pte_t *ptep, pte;
    struct page *old_page = NULL, *new_page = NULL;
    void *kaddr_old, *kaddr_new;
    spinlock_t *ptl;
    int ret = -EINVAL;

    rcu_read_lock();
    task = pid_task(find_vpid(pid), PIDTYPE_PID);
    if (task) get_task_struct(task);
    rcu_read_unlock();
    if (!task) return -ESRCH;

    mm = get_task_mm(task);
    if (!mm) { put_task_struct(task); return -EINVAL; }

    new_page = alloc_page(GFP_HIGHUSER | __GFP_ZERO);
    if (!new_page) { ret = -ENOMEM; goto out_mm; }

    mmap_read_lock(mm);

    pgd = pgd_offset(mm, vaddr);
    if (pgd_none(*pgd) || pgd_bad(*pgd)) goto out_unlock;
    p4d = p4d_offset(pgd, vaddr);
    if (p4d_none(*p4d) || p4d_bad(*p4d)) goto out_unlock;
    pud = pud_offset(p4d, vaddr);
    if (pud_none(*pud) || pud_bad(*pud)) goto out_unlock;
    pmd = pmd_offset(pud, vaddr);
    if (pmd_none(*pmd) || pmd_bad(*pmd)) goto out_unlock;

    ptep = pte_offset_map_lock(mm, pmd, vaddr, &ptl);
    if (!ptep) goto out_unlock;
    pte = *ptep;

    if (!pte_present(pte)) {
        pte_unmap_unlock(ptep, ptl);
        goto out_unlock;
    }

    old_page = pte_page(pte);

    kaddr_old = kmap(old_page);
    kaddr_new = kmap(new_page);
    
    memcpy(kaddr_new, kaddr_old, PAGE_SIZE);
    
    if (copy_from_user((char *)kaddr_new + (vaddr & ~PAGE_MASK), patch_buf, patch_len)) {
        kunmap(new_page); kunmap(old_page); pte_unmap_unlock(ptep, ptl); goto out_unlock;
    }

    kunmap(new_page); kunmap(old_page);

    pte = mk_pte(new_page, pte_pgprot(pte));
    set_pte_at(mm, vaddr, ptep, pte);
    pte_unmap_unlock(ptep, ptl);

    force_flush_tlb_icache();
    ret = 0;
    pr_info("[kpm_shadow] PTE Swap Success! PID: %d, VADDR: 0x%lx\n", pid, vaddr);

out_unlock:
    mmap_read_unlock(mm);
    if (ret != 0 && new_page) __free_page(new_page); 
out_mm:
    mmput(mm); put_task_struct(task); return ret;
}

static int prctl_pre_handler(struct kprobe *p, struct pt_regs *regs)
{
    int option = (int)regs->regs[0];
    if (option == PR_WXSHADOW_PATCH) {
        pid_t pid = (pid_t)regs->regs[1];
        unsigned long vaddr = regs->regs[2];
        void __user *buf = (void __user *)regs->regs[3];
        size_t len = (size_t)regs->regs[4];
        apply_shadow_pte(pid, vaddr, buf, len);
    }
    else if (option == PR_WXSHADOW_RELEASE) {
        pr_info("[kpm_shadow] WXSHADOW_RELEASE Heartbeat OK.\n");
    }
    return 0; 
}

/* 【修改】不再依赖 symbol_name，完全使用传进来的地址 */
static struct kprobe kp = {
    .pre_handler = prctl_pre_handler,
};

static int __init kpm_shadow_init(void)
{
    int ret;
    if (!p_prctl_addr) {
        pr_err("[kpm_shadow] Initialization failed: prctl address not provided.\n");
        return -EINVAL; /* 未传参直接拒绝加载 */
    }

    kp.addr = (kprobe_opcode_t *)p_prctl_addr;
    ret = register_kprobe(&kp);
    if (ret < 0) {
        pr_err("[kpm_shadow] Kprobe install failed at 0x%lx: %d\n", p_prctl_addr, ret);
        return ret;
    }
    pr_info("[kpm_shadow] Engine Activated. Magic prctl hijacked at 0x%lx.\n", p_prctl_addr);
    return 0;
}

static void __exit kpm_shadow_exit(void)
{
    unregister_kprobe(&kp);
    pr_info("[kpm_shadow] Engine Deactivated.\n");
}

module_init(kpm_shadow_init);
module_exit(kpm_shadow_exit);

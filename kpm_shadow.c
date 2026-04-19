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

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Reverse Engineering Expert");
MODULE_DESCRIPTION("Android WuWa - PTE Swap Shadow Page Engine");

/* 用户层下发的魔法指令 */
#define PR_WXSHADOW_PATCH   0x57580006
#define PR_WXSHADOW_RELEASE 0x57580008

/* * 极客流：使用内联汇编强制刷新 TLB 和 I-Cache 
 * 避免高版本 GKI 不导出 flush_tlb_page 等符号导致编译失败
 */
static void force_flush_tlb_icache(void)
{
    asm volatile(
        "dsb ishst\n"        // 确保页表写入完成
        "tlbi vmalle1is\n"   // 使得 Inner Shareable 域内的所有 TLB 失效
        "dsb ish\n"          // 确保 TLB 失效完成
        "isb\n"              // 清空指令流水线
        "ic ialluis\n"       // 使得 Inner Shareable 域内的所有 I-Cache 失效
        "dsb ish\n"
        "isb\n"
        : : : "memory");
}

/*
 * 核心逻辑：PTE 替换 (狸猫换太子)
 */
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

    /* 1. 申请一块干净的高端匿名物理页 */
    new_page = alloc_page(GFP_HIGHUSER | __GFP_ZERO);
    if (!new_page) { ret = -ENOMEM; goto out_mm; }

    mmap_read_lock(mm);

    /* 2. 页表漫游 (Page Table Walk)，寻找目标地址的底层 PTE */
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

    /* 3. 物理层克隆与篡改 */
    kaddr_old = kmap(old_page);
    kaddr_new = kmap(new_page);
    
    // 完整拷贝原物理页的 4KB 数据
    memcpy(kaddr_new, kaddr_old, PAGE_SIZE);
    
    // 在精确的页内偏移处，强行写入用户层传来的 Patch 数据 (比如 B 指令的机器码)
    if (copy_from_user((char *)kaddr_new + (vaddr & ~PAGE_MASK), patch_buf, patch_len)) {
        kunmap(new_page);
        kunmap(old_page);
        pte_unmap_unlock(ptep, ptl);
        goto out_unlock;
    }

    kunmap(new_page);
    kunmap(old_page);

    /* 4. 移花接木：将进程的 PTE 指向我们魔改过的新物理页，保留原有权限 */
    pte = mk_pte(new_page, pte_pgprot(pte));
    set_pte_at(mm, vaddr, ptep, pte);
    
    pte_unmap_unlock(ptep, ptl);

    /* 5. 暴力刷新缓存，让 CPU 乖乖去读新页 */
    force_flush_tlb_icache();

    ret = 0;
    pr_info("[kpm_shadow] PTE Swap Success! PID: %d, VADDR: 0x%lx\n", pid, vaddr);

out_unlock:
    mmap_read_unlock(mm);
    if (ret != 0 && new_page) __free_page(new_page); 
out_mm:
    mmput(mm);
    put_task_struct(task);
    return ret;
}

/*
 * Kprobe 拦截系统调用
 */
static int prctl_pre_handler(struct kprobe *p, struct pt_regs *regs)
{
    /* ARM64 的系统调用参数依次存放在 x0 - x7 寄存器中 */
    int option = (int)regs->regs[0];

    if (option == PR_WXSHADOW_PATCH) {
        pid_t pid = (pid_t)regs->regs[1];
        unsigned long vaddr = regs->regs[2];
        void __user *buf = (void __user *)regs->regs[3];
        size_t len = (size_t)regs->regs[4];

        apply_shadow_pte(pid, vaddr, buf, len);
        
        /* * 我们不强行修改 PC，放行原系统调用。
         * 内核原版的 prctl 不认识 0x57580006，会返回 -EINVAL (22)。
         * 刚好适配用户层 check_kpm() 的 (errno == 22) 存活检测逻辑。
         */
    }
    else if (option == PR_WXSHADOW_RELEASE) {
        pr_info("[kpm_shadow] WXSHADOW_RELEASE Heartbeat OK.\n");
    }

    return 0; // 0 表示放行，继续执行原函数
}

static struct kprobe kp = {
    .symbol_name = "__arm64_sys_prctl",
    .pre_handler = prctl_pre_handler,
};

static int __init kpm_shadow_init(void)
{
    int ret = register_kprobe(&kp);
    if (ret < 0) {
        /* 兼容老版本内核的系统调用命名规范 */
        kp.symbol_name = "sys_prctl";
        ret = register_kprobe(&kp);
        if (ret < 0) {
            pr_err("[kpm_shadow] Kprobe install failed: %d\n", ret);
            return ret;
        }
    }
    pr_info("[kpm_shadow] Engine Activated. Magic prctl hijacked.\n");
    return 0;
}

static void __exit kpm_shadow_exit(void)
{
    unregister_kprobe(&kp);
    pr_info("[kpm_shadow] Engine Deactivated.\n");
}

module_init(kpm_shadow_init);
module_exit(kpm_shadow_exit);

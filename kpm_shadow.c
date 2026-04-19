#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/miscdevice.h>
#include <linux/fs.h>
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
MODULE_DESCRIPTION("Android WuWa - PTE Swap Shadow Page Engine (IOCTL)");

struct pte_patch_req {
    pid_t pid;
    uint64_t addr;
    uint32_t data;
};
#define WUWA_IOCTL_PTE_PATCH _IOW('W', 1, struct pte_patch_req)

/* 异或提取纯净权限位，兼容 5.15 到 6.12 */
#ifndef pte_pgprot
static inline pgprot_t my_pte_pgprot(pte_t pte) {
    return __pgprot(pte_val(pte) ^ pte_val(pfn_pte(pte_pfn(pte), __pgprot(0))));
}
#define pte_pgprot my_pte_pgprot
#endif

/* 核心：PTE 物理层狸猫换太子 */
static int apply_shadow_pte(pid_t pid, unsigned long vaddr, uint32_t patch_data)
{
    /* 【修复点】所有变量声明必须在代码执行前（适配 5.15 的老旧 C 标准） */
    struct task_struct *task;
    struct mm_struct *mm;
    pgd_t *pgd; p4d_t *p4d; pud_t *pud; pmd_t *pmd; pte_t *ptep, pte;
    struct page *old_page = NULL, *new_page = NULL;
    void *kaddr_old, *kaddr_new;
    spinlock_t *ptl;
    int ret = -EINVAL;
    unsigned long raw_pte; /* 提前声明 */

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

    if (!pte_present(pte)) { pte_unmap_unlock(ptep, ptl); goto out_unlock; }

    old_page = pte_page(pte);

    kaddr_old = kmap(old_page);
    kaddr_new = kmap(new_page);
    
    /* 完整克隆原物理页 */
    memcpy(kaddr_new, kaddr_old, PAGE_SIZE);
    
    /* 直接写入机器码数据，此时依然是安全的映射地址 */
    *(uint32_t *)((char *)kaddr_new + (vaddr & ~PAGE_MASK)) = patch_data;

    kunmap(new_page);
    kunmap(old_page);

    /* 重定向 PTE，保留所有 r-xp 等原生权限 */
    pte = mk_pte(new_page, pte_pgprot(pte));
    
    /* * 【核心补丁：击碎 ContPTE 限制】
     * 强制清除第 52 位 (Contiguous bit)，避免 Linux MMU 连续页冲突。
     * 【修复点】这里仅做赋值，不做声明！
     */
    raw_pte = pte_val(pte);
    raw_pte &= ~(1ULL << 52); 

    /* 物理层暴力覆盖，绕过内核 API 屏蔽 */
    *((volatile u64 *)ptep) = raw_pte;

    pte_unmap_unlock(ptep, ptl);

    /* 精准同步屏障 */
    asm volatile(
        "dsb ish\n"
        "tlbi vaae1is, %0\n" 
        "tlbi vmalle1is\n"   
        "dsb ish\n"
        "isb\n"              
        "ic ialluis\n"
        "dsb ish\n"
        "isb\n"
        : : "r" (vaddr >> 12) : "memory");

    ret = 0;
    pr_info("[kpm_shadow] PTE Swap Success! VADDR: 0x%lx, DATA: 0x%x\n", vaddr, patch_data);

out_unlock:
    mmap_read_unlock(mm);
    if (ret != 0 && new_page) __free_page(new_page); 
out_mm:
    mmput(mm); put_task_struct(task); return ret;
}

static long wuwa_ioctl(struct file *file, unsigned int cmd, unsigned long arg)
{
    if (cmd == WUWA_IOCTL_PTE_PATCH) {
        struct pte_patch_req req;
        if (copy_from_user(&req, (void __user *)arg, sizeof(req))) return -EFAULT;
        return apply_shadow_pte(req.pid, req.addr, req.data);
    }
    return -EINVAL;
}

static const struct file_operations wuwa_fops = {
    .owner          = THIS_MODULE,
    .unlocked_ioctl = wuwa_ioctl,
    .compat_ioctl   = wuwa_ioctl,
};

static struct miscdevice wuwa_misc = {
    .minor = MISC_DYNAMIC_MINOR,
    .name  = "wuwa_core",
    .fops  = &wuwa_fops,
};

static int __init kpm_shadow_init(void)
{
    int ret = misc_register(&wuwa_misc);
    if (ret < 0) {
        pr_err("[kpm_shadow] Failed to register device\n");
        return ret;
    }
    pr_info("[kpm_shadow] PTE Shadow Engine Activated. /dev/wuwa_core ready.\n");
    return 0;
}

static void __exit kpm_shadow_exit(void)
{
    misc_deregister(&wuwa_misc);
    pr_info("[kpm_shadow] Engine Deactivated.\n");
}

module_init(kpm_shadow_init);
module_exit(kpm_shadow_exit);

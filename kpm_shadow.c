#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/sched.h>
#include <linux/sched/mm.h>
#include <linux/mm.h>
#include <linux/uaccess.h>
#include <linux/highmem.h>
#include <asm/pgtable.h>
#include <asm/tlbflush.h>
#include <linux/pgtable.h>
#include <net/sock.h>
#include <linux/netlink.h>
#include <linux/skbuff.h>
#include <net/net_namespace.h>

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Reverse Engineering Expert");
MODULE_DESCRIPTION("Android WuWa - Fileless Netlink Shadow Engine");

/* 定义一个不与系统冲突的独立协议号 (29 通常无人使用) */
#define NETLINK_WUWA 29 

struct pte_patch_req {
    pid_t pid;
    uint64_t addr;
    uint32_t data;
};

struct sock *nl_sk = NULL;

#ifndef pte_pgprot
static inline pgprot_t my_pte_pgprot(pte_t pte) {
    return __pgprot(pte_val(pte) ^ pte_val(pfn_pte(pte_pfn(pte), __pgprot(0))));
}
#define pte_pgprot my_pte_pgprot
#endif

static int apply_shadow_pte(pid_t pid, unsigned long vaddr, uint32_t patch_data)
{
    struct task_struct *task;
    struct mm_struct *mm;
    pgd_t *pgd; p4d_t *p4d; pud_t *pud; pmd_t *pmd; pte_t *ptep, pte;
    struct page *old_page = NULL, *new_page = NULL;
    void *kaddr_old, *kaddr_new;
    spinlock_t *ptl;
    int ret = -EINVAL;
    unsigned long raw_pte;

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
    memcpy(kaddr_new, kaddr_old, PAGE_SIZE);
    
    *(uint32_t *)((char *)kaddr_new + (vaddr & ~PAGE_MASK)) = patch_data;

    kunmap(new_page);
    kunmap(old_page);

    pte = mk_pte(new_page, pte_pgprot(pte));
    raw_pte = pte_val(pte);
    raw_pte &= ~(1ULL << 52); 

    *((volatile u64 *)ptep) = raw_pte;
    pte_unmap_unlock(ptep, ptl);

    asm volatile("dsb ish\ntlbi vaae1is, %0\ntlbi vmalle1is\ndsb ish\nisb\nic ialluis\ndsb ish\nisb\n" : : "r" (vaddr >> 12) : "memory");
    ret = 0;

out_unlock:
    mmap_read_unlock(mm);
    if (ret != 0 && new_page) __free_page(new_page); 
out_mm:
    mmput(mm); put_task_struct(task); return ret;
}

/* 核心通信槽：拦截网络栈传来的假数据包 */
static void nl_recv_msg(struct sk_buff *skb)
{
    struct nlmsghdr *nlh;
    struct pte_patch_req *req;

    if (skb->len >= nlmsg_total_size(0)) {
        nlh = nlmsg_hdr(skb);
        if (nlmsg_len(nlh) >= sizeof(struct pte_patch_req)) {
            req = (struct pte_patch_req *)nlmsg_data(nlh);
            /* 收到来自用户态的数据包，触发底层的影子页物理劫持 */
            apply_shadow_pte(req->pid, req->addr, req->data);
        }
    }
}

static int __init kpm_shadow_init(void)
{
    struct netlink_kernel_cfg cfg = {
        .input = nl_recv_msg,
    };
    
    nl_sk = netlink_kernel_create(&init_net, NETLINK_WUWA, &cfg);
    if (!nl_sk) {
        pr_err("[kpm_shadow] Failed to create netlink socket.\n");
        return -ENOMEM;
    }
    
    pr_info("[kpm_shadow] Fileless Netlink Engine Activated. Listening on proto 29.\n");
    return 0;
}

static void __exit kpm_shadow_exit(void)
{
    if (nl_sk) {
        netlink_kernel_release(nl_sk);
    }
    pr_info("[kpm_shadow] Engine Deactivated.\n");
}

module_init(kpm_shadow_init);
module_exit(kpm_shadow_exit);

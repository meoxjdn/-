#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/sched.h>
#include <linux/mm.h>
#include <linux/uaccess.h>
#include <linux/highmem.h>
#include <asm/pgtable.h>
#include <asm/tlbflush.h>
#include <linux/pgtable.h>
#include <net/sock.h>
#include <linux/netlink.h>
#include <linux/skbuff.h>
#include <linux/percpu.h>
#include <net/net_namespace.h>

MODULE_LICENSE("GPL");
MODULE_AUTHOR("RX_Engine");
MODULE_DESCRIPTION("Dynamic R^X Shadow Page Engine V3");

static unsigned long long k_do_fault = 0;
module_param(k_do_fault, ullong, 0444);

static unsigned long long k_init_mm = 0;
module_param(k_init_mm, ullong, 0444);

#define NETLINK_WUWA 29 

#ifndef ESR_ELx_EC_SHIFT
#define ESR_ELx_EC_SHIFT    26
#endif
#ifndef EC_INSN_ABORT_L
#define EC_INSN_ABORT_L     0x20  
#endif
#ifndef EC_DATA_ABORT_L
#define EC_DATA_ABORT_L     0x24  
#endif
#ifndef PTE_USER_XN
#define PTE_USER_XN      (1ULL << 54) 
#endif
#ifndef PTE_AP_READ_ONLY
#define PTE_AP_READ_ONLY (3ULL << 6)  
#endif

struct rx_patch_req {
    pid_t pid;
    uint64_t addr;
    uint32_t data;
};

static struct sock *nl_sk = NULL;
static uint64_t g_target_vaddr = 0;
static uint64_t g_orig_pfn = 0;
static uint64_t g_shadow_pfn = 0;
static struct mm_struct *g_game_mm = NULL;
static bool g_kernel_hooked = false;

/* 防递归死机锁：每个 CPU 核心独立保存状态 */
static DEFINE_PER_CPU(int, g_in_hook);

#ifndef pte_pgprot
static inline pgprot_t my_pte_pgprot(pte_t pte) {
    return __pgprot(pte_val(pte) ^ pte_val(pfn_pte(pte_pfn(pte), __pgprot(0))));
}
#define pte_pgprot my_pte_pgprot
#endif

/* 魔法逃逸舱：在代码段中硬开辟的纯执行空间，免疫 PXN 异常 */
__attribute__((naked)) void my_escape_pod(void) {
    asm volatile(
        "nop\nnop\nnop\nnop\n"
        "nop\nnop\nnop\nnop\n"
    );
}

static pte_t* get_pte_ptr(struct mm_struct *mm, unsigned long vaddr) {
    pgd_t *pgd; p4d_t *p4d; pud_t *pud; pmd_t *pmd; pte_t *ptep;
    pgd = pgd_offset(mm, vaddr);
    if (pgd_none(*pgd) || pgd_bad(*pgd)) return NULL;
    p4d = p4d_offset(pgd, vaddr);
    if (p4d_none(*p4d) || p4d_bad(*p4d)) return NULL;
    pud = pud_offset(p4d, vaddr);
    if (pud_none(*pud) || pud_bad(*pud)) return NULL;
    pmd = pmd_offset(pud, vaddr);
    if (pmd_none(*pmd) || pmd_bad(*pmd)) return NULL;
    ptep = pte_offset_map(pmd, vaddr);
    return ptep;
}

static void force_flush_tlb_page(unsigned long vaddr) {
    asm volatile("dsb ish\ntlbi vaae1is, %0\ntlbi vmalle1is\ndsb ish\nisb\nic ialluis\ndsb ish\nisb\n" : : "r" (vaddr >> 12) : "memory");
}

int my_fault_dispatcher(unsigned long addr, unsigned int esr, struct pt_regs *regs) {
    unsigned int ec;
    pte_t *ptep;
    unsigned long raw_pte;
    pte_t new_pte;
    int *hook_flag;

    if (!g_target_vaddr || (addr & PAGE_MASK) != (g_target_vaddr & PAGE_MASK)) return 0; 

    /* 防死机护盾：如果当前核心已经在处理异常，直接放行，避免无限套娃 */
    hook_flag = this_cpu_ptr(&g_in_hook);
    if (*hook_flag) return 0;
    *hook_flag = 1;

    ec = esr >> ESR_ELx_EC_SHIFT;
    ptep = get_pte_ptr(g_game_mm, g_target_vaddr);
    if (!ptep) {
        *hook_flag = 0;
        return 0;
    }

    if (ec == EC_INSN_ABORT_L) {
        new_pte = pfn_pte(g_shadow_pfn, pte_pgprot(*ptep));
        raw_pte = pte_val(new_pte);
        raw_pte &= ~PTE_USER_XN;       // 给执行权限
        raw_pte |= PTE_AP_READ_ONLY;   // 【兼容性降维】暂时保留读取，防止硬件死锁
        raw_pte &= ~(1ULL << 52);      
        *((volatile u64 *)ptep) = raw_pte;
        force_flush_tlb_page(g_target_vaddr);
        *hook_flag = 0;
        return 1;
    } else if (ec == EC_DATA_ABORT_L) {
        new_pte = pfn_pte(g_orig_pfn, pte_pgprot(*ptep));
        raw_pte = pte_val(new_pte);
        raw_pte |= PTE_USER_XN;        // 剥夺执行权限
        raw_pte |= PTE_AP_READ_ONLY;   // 给读取权限
        raw_pte &= ~(1ULL << 52);
        *((volatile u64 *)ptep) = raw_pte;
        force_flush_tlb_page(g_target_vaddr);
        *hook_flag = 0;
        return 1;
    }
    
    *hook_flag = 0;
    return 0;
}

__attribute__((naked)) void my_fault_trampoline(void) {
    asm volatile(
        "stp x0, x1, [sp, #-16]!\n"
        "stp x2, x3, [sp, #-16]!\n"
        "stp x4, x5, [sp, #-16]!\n"
        "stp x6, x7, [sp, #-16]!\n"
        "stp x8, x9, [sp, #-16]!\n"
        "stp x10, x11, [sp, #-16]!\n"
        "stp x12, x13, [sp, #-16]!\n"
        "stp x14, x15, [sp, #-16]!\n"
        "stp x16, x17, [sp, #-16]!\n"
        "stp x18, x19, [sp, #-16]!\n"
        "stp x29, x30, [sp, #-16]!\n"
        "bl my_fault_dispatcher\n"
        "cmp x0, #1\n"
        "b.eq .L_handled\n"
        "ldp x29, x30, [sp], #16\n"
        "ldp x18, x19, [sp], #16\n"
        "ldp x16, x17, [sp], #16\n"
        "ldp x14, x15, [sp], #16\n"
        "ldp x12, x13, [sp], #16\n"
        "ldp x10, x11, [sp], #16\n"
        "ldp x8, x9, [sp], #16\n"
        "ldp x6, x7, [sp], #16\n"
        "ldp x4, x5, [sp], #16\n"
        "ldp x2, x3, [sp], #16\n"
        "ldp x0, x1, [sp], #16\n"
        "ldr x16, =my_escape_pod\n" // 指向免疫 PXN 的代码段逃逸舱
        "br x16\n"
        ".L_handled:\n"
        "ldp x29, x30, [sp], #16\n"
        "ldp x18, x19, [sp], #16\n"
        "ldp x16, x17, [sp], #16\n"
        "ldp x14, x15, [sp], #16\n"
        "ldp x12, x13, [sp], #16\n"
        "ldp x10, x11, [sp], #16\n"
        "ldp x8, x9, [sp], #16\n"
        "ldp x6, x7, [sp], #16\n"
        "ldp x4, x5, [sp], #16\n"
        "ldp x2, x3, [sp], #16\n"
        "ldp x0, x1, [sp], #16\n"
        "eret\n" 
    );
}

static int inject_and_setup_rx(struct rx_patch_req *req) {
    struct task_struct *task;
    struct mm_struct *mm;
    struct page *orig_page, *shadow_page, *new_kpage, *pod_page;
    void *kaddr_orig, *kaddr_shadow, *kaddr_new_kernel, *pod_kaddr;
    pte_t *game_ptep, *kernel_ptep, *pod_ptep;
    unsigned long flags;
    unsigned long raw_game_pte;
    unsigned long offset;
    uint32_t *patch_addr;
    uint32_t *pod_ptr;
    unsigned long raw_kpte;

    /* 清理模式检测 */
    if (req->addr == 0) {
        if (g_target_vaddr && g_game_mm) {
            game_ptep = get_pte_ptr(g_game_mm, g_target_vaddr);
            if (game_ptep) {
                raw_game_pte = pte_val(pfn_pte(g_orig_pfn, pte_pgprot(*game_ptep)));
                raw_game_pte &= ~(1ULL << 52);
                *((volatile u64 *)game_ptep) = raw_game_pte;
                force_flush_tlb_page(g_target_vaddr);
            }
            g_target_vaddr = 0;
            pr_info("[RX] Address Cleanup Done.\n");
        }
        return 0;
    }

    if (!k_do_fault || !k_init_mm) return -EINVAL;

    rcu_read_lock();
    task = pid_task(find_vpid(req->pid), PIDTYPE_PID);
    if (task) get_task_struct(task);
    rcu_read_unlock();
    if (!task) return -ESRCH;

    mm = get_task_mm(task);
    if (!mm) { put_task_struct(task); return -EINVAL; }
    
    g_game_mm = mm;
    g_target_vaddr = req->addr;

    game_ptep = get_pte_ptr(mm, g_target_vaddr);
    if (!game_ptep) goto out;

    orig_page = pte_page(*game_ptep);
    g_orig_pfn = page_to_pfn(orig_page);

    shadow_page = alloc_page(GFP_HIGHUSER | __GFP_ZERO);
    g_shadow_pfn = page_to_pfn(shadow_page);
    
    kaddr_orig = kmap(orig_page);
    kaddr_shadow = kmap(shadow_page);
    memcpy(kaddr_shadow, kaddr_orig, PAGE_SIZE);
    *(uint32_t *)((char *)kaddr_shadow + (g_target_vaddr & ~PAGE_MASK)) = req->data;
    kunmap(shadow_page);
    kunmap(orig_page);

    raw_game_pte = pte_val(*game_ptep);
    raw_game_pte |= PTE_USER_XN;
    *((volatile u64 *)game_ptep) = raw_game_pte;
    force_flush_tlb_page(g_target_vaddr);

    if (!g_kernel_hooked) {
        /* 魔法写保护击穿：将汇编代码强制写入自身的代码段逃逸舱 */
        pod_ptep = get_pte_ptr((struct mm_struct *)k_init_mm, (unsigned long)my_escape_pod);
        if (pod_ptep) {
            pod_page = pte_page(*pod_ptep);
            pod_kaddr = kmap(pod_page);
            offset = (unsigned long)my_escape_pod & ~PAGE_MASK;
            pod_ptr = (uint32_t *)((char *)pod_kaddr + offset);
            
            memcpy(pod_ptr, (void *)k_do_fault, 16);
            pod_ptr[4] = 0x58000050; // LDR X16, #8
            pod_ptr[5] = 0xD61F0200; // BR X16
            *((uint64_t *)&pod_ptr[6]) = k_do_fault + 16;
            
            kunmap(pod_page);
            force_flush_tlb_page((unsigned long)my_escape_pod);
        }

        /* 开始常规的内核拦截跳板搭建 */
        kernel_ptep = get_pte_ptr((struct mm_struct *)k_init_mm, k_do_fault);
        if (!kernel_ptep) goto out;

        new_kpage = alloc_page(GFP_KERNEL | __GFP_ZERO);
        kaddr_new_kernel = page_address(new_kpage);
        memcpy(kaddr_new_kernel, (void *)(k_do_fault & PAGE_MASK), PAGE_SIZE);

        offset = k_do_fault & ~PAGE_MASK;
        patch_addr = (uint32_t *)((char *)kaddr_new_kernel + offset);
        
        patch_addr[0] = 0x58000050; 
        patch_addr[1] = 0xD61F0200; 
        *((uint64_t *)&patch_addr[2]) = (uint64_t)my_fault_trampoline;

        raw_kpte = pte_val(pfn_pte(page_to_pfn(new_kpage), pte_pgprot(*kernel_ptep)));
        raw_kpte &= ~(1ULL << 52); 

        local_irq_save(flags); 
        *((volatile u64 *)kernel_ptep) = raw_kpte;
        asm volatile("dsb ishst\ntlbi vmalle1is\ndsb ish\nisb\nic ialluis\ndsb ish\nisb\n" ::: "memory");
        local_irq_restore(flags); 
        
        g_kernel_hooked = true;
        pr_info("[RX] Kernel Hook Injected with Safe Pod\n");
    }

out:
    mmput(mm); put_task_struct(task);
    return 0;
}

static void nl_recv_msg(struct sk_buff *skb) {
    struct nlmsghdr *nlh;
    struct rx_patch_req *req;

    if (skb->len >= nlmsg_total_size(0)) {
        nlh = nlmsg_hdr(skb);
        if (nlmsg_len(nlh) >= sizeof(struct rx_patch_req)) {
            req = (struct rx_patch_req *)NLMSG_DATA(nlh);
            inject_and_setup_rx(req);
        }
    }
}

static int __init rx_shadow_init(void) {
    struct netlink_kernel_cfg cfg = { .input = nl_recv_msg, };
    nl_sk = netlink_kernel_create(&init_net, NETLINK_WUWA, &cfg);
    if (!nl_sk) return -ENOMEM;
    return 0;
}

static void __exit rx_shadow_exit(void) {
    if (nl_sk) netlink_kernel_release(nl_sk);
}

module_init(rx_shadow_init);
module_exit(rx_shadow_exit);

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
#include <net/net_namespace.h>

MODULE_LICENSE("GPL");
MODULE_AUTHOR("RX_Engine");
MODULE_DESCRIPTION("Dynamic R^X Shadow Page Engine");

/* --- 接收装载脚本传入的内核地址 --- */
static unsigned long long k_do_fault = 0;
module_param(k_do_fault, ullong, 0444);

static unsigned long long k_init_mm = 0;
module_param(k_init_mm, ullong, 0444);

#define NETLINK_WUWA 29 

/* --- 宏定义护盾：完美适配新老内核 --- */
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

/* 【核心修复】：删除 static，将逃逸舱暴露为全局符号，供汇编指令 ldr 调用 */
uint8_t g_trampoline_escape_pod[32]; 

#ifndef pte_pgprot
static inline pgprot_t my_pte_pgprot(pte_t pte) {
    return __pgprot(pte_val(pte) ^ pte_val(pfn_pte(pte_pfn(pte), __pgprot(0))));
}
#define pte_pgprot my_pte_pgprot
#endif

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

    if (!g_target_vaddr || (addr & PAGE_MASK) != (g_target_vaddr & PAGE_MASK)) return 0; 

    ec = esr >> ESR_ELx_EC_SHIFT;
    ptep = get_pte_ptr(g_game_mm, g_target_vaddr);
    if (!ptep) return 0;

    if (ec == EC_INSN_ABORT_L) {
        new_pte = pfn_pte(g_shadow_pfn, pte_pgprot(*ptep));
        raw_pte = pte_val(new_pte);
        raw_pte &= ~PTE_USER_XN;       
        raw_pte &= ~(1ULL << 52);      
        *((volatile u64 *)ptep) = raw_pte;
        force_flush_tlb_page(g_target_vaddr);
        return 1;
    } else if (ec == EC_DATA_ABORT_L) {
        new_pte = pfn_pte(g_orig_pfn, pte_pgprot(*ptep));
        raw_pte = pte_val(new_pte);
        raw_pte |= PTE_USER_XN;        
        raw_pte |= PTE_AP_READ_ONLY;   
        raw_pte &= ~(1ULL << 52);
        *((volatile u64 *)ptep) = raw_pte;
        force_flush_tlb_page(g_target_vaddr);
        return 1;
    }
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
        "ldr x16, =g_trampoline_escape_pod\n" 
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
    struct page *orig_page, *shadow_page, *new_kpage;
    void *kaddr_orig, *kaddr_shadow, *kaddr_new_kernel;
    pte_t *game_ptep, *kernel_ptep;
    unsigned long flags;
    unsigned long raw_game_pte;
    unsigned long offset;
    uint32_t *patch_addr;
    uint32_t *escape_tail;
    unsigned long raw_kpte;

    if (!k_do_fault || !k_init_mm) {
        pr_err("[RX] Kernel pointers missing!\n");
        return -EINVAL;
    }

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
        kernel_ptep = get_pte_ptr((struct mm_struct *)k_init_mm, k_do_fault);
        if (!kernel_ptep) goto out;

        new_kpage = alloc_page(GFP_KERNEL | __GFP_ZERO);
        kaddr_new_kernel = page_address(new_kpage);
        memcpy(kaddr_new_kernel, (void *)(k_do_fault & PAGE_MASK), PAGE_SIZE);

        offset = k_do_fault & ~PAGE_MASK;
        patch_addr = (uint32_t *)((char *)kaddr_new_kernel + offset);
        
        memcpy(g_trampoline_escape_pod, patch_addr, 16);
        
        escape_tail = (uint32_t *)(g_trampoline_escape_pod + 16);
        escape_tail[0] = 0x58000050; 
        escape_tail[1] = 0xD61F0200; 
        *((uint64_t *)&escape_tail[2]) = k_do_fault + 16;

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
        pr_info("[RX] Kernel Hook Injected\n");
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
            pr_info("[RX] Target: 0x%llx\n", req->addr);
            inject_and_setup_rx(req);
        }
    }
}

static int __init rx_shadow_init(void) {
    struct netlink_kernel_cfg cfg = { .input = nl_recv_msg, };
    nl_sk = netlink_kernel_create(&init_net, NETLINK_WUWA, &cfg);
    if (!nl_sk) return -ENOMEM;
    pr_info("[RX] Engine Ready (k_do_fault=0x%llx)\n", k_do_fault);
    return 0;
}

static void __exit rx_shadow_exit(void) {
    if (nl_sk) netlink_kernel_release(nl_sk);
    pr_info("[RX] Unloaded\n");
}

module_init(rx_shadow_init);
module_exit(rx_shadow_exit);

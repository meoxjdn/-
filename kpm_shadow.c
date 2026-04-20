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
MODULE_DESCRIPTION("KPM-Derived Standalone R^X Engine V6");

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
#ifndef PTE_VALID
#define PTE_VALID        (1ULL << 0)
#endif
#ifndef PTE_TYPE_PAGE
#define PTE_TYPE_PAGE    (3ULL << 0)
#endif
#ifndef PTE_USER
#define PTE_USER         (1ULL << 6)   
#endif
#ifndef PTE_RDONLY
#define PTE_RDONLY       (1ULL << 7)   
#endif
#ifndef PTE_AF
#define PTE_AF           (1ULL << 10)
#endif
#ifndef PTE_NG
#define PTE_NG           (1ULL << 11)
#endif
#ifndef PTE_PXN
#define PTE_PXN          (1ULL << 53)
#endif
#ifndef PTE_UXN
#define PTE_UXN          (1ULL << 54)
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

static DEFINE_PER_CPU(int, g_in_hook);

/* 代码段逃逸舱，预留充足空间 */
__attribute__((naked)) void my_escape_pod(void) {
    asm volatile(
        "nop\nnop\nnop\nnop\n"
        "nop\nnop\nnop\nnop\n"
        "nop\nnop\nnop\nnop\n"
    );
}

/* 狙击级 TLB 刷新 */
static inline void kpm_tlbi_page(unsigned long uaddr) {
    asm volatile(
        "dsb ishst\n"
        "tlbi vaale1is, %0\n"
        "dsb ish\n"
        "isb\n"
        : : "r"(uaddr >> 12) : "memory"
    );
}

static u64 make_pte(unsigned long pfn, u64 prot) {
    return (pfn << PAGE_SHIFT) | prot | PTE_VALID | PTE_TYPE_PAGE | PTE_AF | (3ULL << 8) | PTE_NG;
}

static pte_t* get_user_pte_safe(struct mm_struct *mm, unsigned long vaddr) {
    pgd_t *pgd; p4d_t *p4d; pud_t *pud; pmd_t *pmd; pte_t *ptep;
    
    /* 【防崩溃核心】：确保当前处于正确的进程上下文，防止 mm 被意外释放 */
    if (!current->mm || current->mm != g_game_mm) return NULL;

    pgd = pgd_offset(mm, vaddr);
    if (pgd_none(*pgd) || pgd_bad(*pgd)) return NULL;
    p4d = p4d_offset(pgd, vaddr);
    if (p4d_none(*p4d) || p4d_bad(*p4d)) return NULL;
    pud = pud_offset(p4d, vaddr);
    if (pud_none(*pud) || pud_bad(*pud)) return NULL;
    pmd = pmd_offset(pud, vaddr);
    if (pmd_none(*pmd)) return NULL;
    
    /* 拒绝处理 2MB Huge Page */
    if ((pte_val(*(pte_t*)pmd) & 3) == 1) return NULL; 
    
    ptep = pte_offset_map(pmd, vaddr);
    return ptep;
}

int my_fault_dispatcher(unsigned long addr, unsigned int esr, struct pt_regs *regs) {
    unsigned int ec;
    pte_t *ptep;
    u64 entry;
    unsigned long flags;

    if (!g_target_vaddr || (addr & PAGE_MASK) != (g_target_vaddr & PAGE_MASK)) return 0; 

    /* 【死锁修复】：关闭本地 CPU 中断，防止线程被抢占导致 g_in_hook 永久锁死 */
    local_irq_save(flags);
    if (__this_cpu_read(g_in_hook)) {
        local_irq_restore(flags);
        return 0;
    }
    __this_cpu_write(g_in_hook, 1);

    ptep = get_user_pte_safe(g_game_mm, g_target_vaddr);
    if (!ptep) {
        __this_cpu_write(g_in_hook, 0);
        local_irq_restore(flags);
        return 0;
    }

    ec = esr >> ESR_ELx_EC_SHIFT;

    if (ec == EC_INSN_ABORT_L) {
        entry = make_pte(g_shadow_pfn, 0); 
        
        /* 【BBM 硬件铁律】：切换页表必须先置零，后刷新，再写入，否则必触发 SError 卡死 */
        *((volatile u64 *)ptep) = 0;
        kpm_tlbi_page(g_target_vaddr);
        *((volatile u64 *)ptep) = entry;
        kpm_tlbi_page(g_target_vaddr);
        
        __this_cpu_write(g_in_hook, 0);
        local_irq_restore(flags);
        return 1;
    } else if (ec == EC_DATA_ABORT_L) {
        entry = make_pte(g_orig_pfn, PTE_USER | PTE_RDONLY | PTE_UXN);
        
        /* 【BBM 硬件铁律】 */
        *((volatile u64 *)ptep) = 0;
        kpm_tlbi_page(g_target_vaddr);
        *((volatile u64 *)ptep) = entry;
        kpm_tlbi_page(g_target_vaddr);
        
        __this_cpu_write(g_in_hook, 0);
        local_irq_restore(flags);
        return 1;
    }
    
    __this_cpu_write(g_in_hook, 0);
    local_irq_restore(flags);
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
        "ldr x16, =my_escape_pod\n" 
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
        "ret\n"
    );
}

static int inject_and_setup_rx(struct rx_patch_req *req) {
    struct task_struct *task;
    struct mm_struct *mm;
    struct page *orig_page, *shadow_page, *new_kpage, *pod_page;
    void *kaddr_orig, *kaddr_shadow, *kaddr_new_kernel, *pod_kaddr;
    pte_t *game_ptep, *kernel_ptep, *pod_ptep;
    unsigned long flags, offset, pod_offset;
    uint32_t *patch_addr, *pod_ptr, *orig_ptr;
    u64 entry, raw_kpte;

    if (req->addr == 0) {
        if (g_target_vaddr && g_game_mm) {
            game_ptep = get_user_pte_safe(g_game_mm, g_target_vaddr);
            if (game_ptep) {
                entry = make_pte(g_orig_pfn, PTE_USER | PTE_UXN); 
                *((volatile u64 *)game_ptep) = 0; /* BBM */
                kpm_tlbi_page(g_target_vaddr);
                *((volatile u64 *)game_ptep) = entry;
                kpm_tlbi_page(g_target_vaddr);
            }
            g_target_vaddr = 0;
            pr_info("[RX] KPM Mode Cleaned up.\n");
        }
        return 0;
    }

    if (!k_do_fault || !k_init_mm) return -EINVAL;

    if (g_target_vaddr == req->addr && g_shadow_pfn != 0) {
        kaddr_shadow = kmap(pfn_to_page(g_shadow_pfn));
        *(uint32_t *)((char *)kaddr_shadow + (g_target_vaddr & ~PAGE_MASK)) = req->data;
        kunmap(pfn_to_page(g_shadow_pfn));
        kpm_tlbi_page(g_target_vaddr);
        pr_info("[RX] Updated data for existing target.\n");
        return 0;
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

    game_ptep = get_user_pte_safe(mm, g_target_vaddr);
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

    entry = make_pte(g_orig_pfn, PTE_USER | PTE_RDONLY | PTE_UXN);
    *((volatile u64 *)game_ptep) = 0; /* BBM */
    kpm_tlbi_page(g_target_vaddr);
    *((volatile u64 *)game_ptep) = entry;
    kpm_tlbi_page(g_target_vaddr);

    if (!g_kernel_hooked) {
        pod_ptep = pte_offset_kernel((pmd_t *)k_init_mm, (unsigned long)my_escape_pod);
        if (pod_ptep) {
            pod_page = pte_page(*pod_ptep);
            pod_kaddr = kmap(pod_page);
            pod_offset = (unsigned long)my_escape_pod & ~PAGE_MASK;
            pod_ptr = (uint32_t *)((char *)pod_kaddr + pod_offset);
            orig_ptr = (uint32_t *)(k_do_fault & ~3UL);
            
            /* 【PAC 坠机终极修复】：强制注入 BTI J 着陆垫，并偏移取指令防止 PAC 双重加密 */
            pod_ptr[0] = 0xD503249F;  // BTI J: 防止内核跳转安全检测蓝屏
            pod_ptr[1] = orig_ptr[1]; // 拷贝 +4
            pod_ptr[2] = orig_ptr[2]; // 拷贝 +8
            pod_ptr[3] = orig_ptr[3]; // 拷贝 +12
            pod_ptr[4] = orig_ptr[4]; // 拷贝 +16
            
            pod_ptr[5] = 0x58000050; // LDR X16, #8
            pod_ptr[6] = 0xD61F0200; // BR X16
            *((uint64_t *)&pod_ptr[7]) = k_do_fault + 20; // 对应偏移跳回
            
            kunmap(pod_page);
            kpm_tlbi_page((unsigned long)my_escape_pod);
            asm volatile("ic ivau, %0\n dsb ish\n isb\n" : : "r" (my_escape_pod) : "memory");
        }

        kernel_ptep = pte_offset_kernel((pmd_t *)k_init_mm, k_do_fault); 
        if (!kernel_ptep) goto out;

        new_kpage = alloc_page(GFP_KERNEL | __GFP_ZERO);
        kaddr_new_kernel = page_address(new_kpage);
        memcpy(kaddr_new_kernel, (void *)(k_do_fault & PAGE_MASK), PAGE_SIZE);

        offset = k_do_fault & ~PAGE_MASK;
        patch_addr = (uint32_t *)((char *)kaddr_new_kernel + offset);
        
        patch_addr[1] = 0x58000050; 
        patch_addr[2] = 0xD61F0200; 
        *((uint64_t *)&patch_addr[3]) = (uint64_t)my_fault_trampoline;

        raw_kpte = (page_to_pfn(new_kpage) << PAGE_SHIFT) | (pte_val(*kernel_ptep) & 0x0000FFFFFFFFF000UL) | PTE_VALID | PTE_AF | PTE_NG;
        raw_kpte &= ~(1ULL << 52); 

        local_irq_save(flags); 
        *((volatile u64 *)kernel_ptep) = raw_kpte;
        asm volatile("dsb ishst\ntlbi vmalle1is\ndsb ish\nisb\nic ialluis\ndsb ish\nisb\n" ::: "memory");
        local_irq_restore(flags); 
        
        g_kernel_hooked = true;
        pr_info("[RX] KPM Standalone Engine V6 Online.\n");
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
    return nl_sk ? 0 : -ENOMEM;
}

static void __exit rx_shadow_exit(void) {
    if (nl_sk) netlink_kernel_release(nl_sk);
}

module_init(rx_shadow_init);
module_exit(rx_shadow_exit);

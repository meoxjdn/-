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
MODULE_DESCRIPTION("KPM Standalone R^X Engine V7 - Multi-Track");

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

/* --- 核心升级：多轨并发追踪阵列 --- */
#define MAX_RX_PAGES 32
struct rx_page {
    uint64_t vaddr;
    uint64_t orig_pfn;
    uint64_t shadow_pfn;
    bool active;
};
static struct rx_page g_rx_pages[MAX_RX_PAGES];

static struct sock *nl_sk = NULL;
static struct mm_struct *g_game_mm = NULL;
static bool g_kernel_hooked = false;

static DEFINE_PER_CPU(int, g_in_hook);

/* 代码段逃逸舱 */
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

/* 修复点：移除了会导致 Netlink 失败的上下文检查 */
static pte_t* get_user_pte_safe(struct mm_struct *mm, unsigned long vaddr) {
    pgd_t *pgd; p4d_t *p4d; pud_t *pud; pmd_t *pmd; pte_t *ptep;
    
    if (!mm) return NULL;

    pgd = pgd_offset(mm, vaddr);
    if (pgd_none(*pgd) || pgd_bad(*pgd)) return NULL;
    p4d = p4d_offset(pgd, vaddr);
    if (p4d_none(*p4d) || p4d_bad(*p4d)) return NULL;
    pud = pud_offset(p4d, vaddr);
    if (pud_none(*pud) || pud_bad(*pud)) return NULL;
    pmd = pmd_offset(pud, vaddr);
    if (pmd_none(*pmd)) return NULL;
    
    /* 拒绝 2MB 大页 */
    if ((pte_val(*(pte_t*)pmd) & 3) == 1) return NULL; 
    
    ptep = pte_offset_map(pmd, vaddr);
    return ptep;
}

int my_fault_dispatcher(unsigned long addr, unsigned int esr, struct pt_regs *regs) {
    unsigned int ec;
    pte_t *ptep;
    u64 entry;
    unsigned long flags;
    struct rx_page *p = NULL;
    int i;

    /* 多轨匹配：看触发异常的地址是否在我们的保护名单里 */
    for (i = 0; i < MAX_RX_PAGES; i++) {
        if (g_rx_pages[i].active && (addr & PAGE_MASK) == g_rx_pages[i].vaddr) {
            p = &g_rx_pages[i];
            break;
        }
    }
    if (!p) return 0; 

    local_irq_save(flags);
    if (__this_cpu_read(g_in_hook)) {
        local_irq_restore(flags);
        return 0;
    }
    __this_cpu_write(g_in_hook, 1);

    ptep = get_user_pte_safe(g_game_mm, p->vaddr);
    if (!ptep) {
        __this_cpu_write(g_in_hook, 0);
        local_irq_restore(flags);
        return 0;
    }

    ec = esr >> ESR_ELx_EC_SHIFT;

    if (ec == EC_INSN_ABORT_L) {
        entry = make_pte(p->shadow_pfn, 0); 
        *((volatile u64 *)ptep) = 0;
        kpm_tlbi_page(p->vaddr);
        *((volatile u64 *)ptep) = entry;
        kpm_tlbi_page(p->vaddr);
        
        __this_cpu_write(g_in_hook, 0);
        local_irq_restore(flags);
        return 1;
    } else if (ec == EC_DATA_ABORT_L) {
        entry = make_pte(p->orig_pfn, PTE_USER | PTE_RDONLY | PTE_UXN);
        *((volatile u64 *)ptep) = 0;
        kpm_tlbi_page(p->vaddr);
        *((volatile u64 *)ptep) = entry;
        kpm_tlbi_page(p->vaddr);
        
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
    int i;
    struct rx_page *p = NULL;

    /* 清理还原逻辑 (遍历所有槽位) */
    if (req->addr == 0) {
        for (i = 0; i < MAX_RX_PAGES; i++) {
            if (g_rx_pages[i].active && g_game_mm) {
                game_ptep = get_user_pte_safe(g_game_mm, g_rx_pages[i].vaddr);
                if (game_ptep) {
                    /* 还原为普通代码段：用户可执行、只读 (r-xp) */
                    entry = make_pte(g_rx_pages[i].orig_pfn, PTE_USER | PTE_RDONLY); 
                    *((volatile u64 *)game_ptep) = 0; 
                    kpm_tlbi_page(g_rx_pages[i].vaddr);
                    *((volatile u64 *)game_ptep) = entry;
                    kpm_tlbi_page(g_rx_pages[i].vaddr);
                }
                __free_page(pfn_to_page(g_rx_pages[i].shadow_pfn));
                g_rx_pages[i].active = false;
            }
        }
        pr_info("[RX] All KPM Modes Cleaned up.\n");
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

    /* 核心 1：检查是否页面已经存在于保护名单 */
    for (i = 0; i < MAX_RX_PAGES; i++) {
        if (g_rx_pages[i].active && g_rx_pages[i].vaddr == (req->addr & PAGE_MASK)) {
            p = &g_rx_pages[i];
            break;
        }
    }

    if (p) {
        /* 如果页面已存在，只需要更新影子页里的代码即可，无需重绑 PTE */
        kaddr_shadow = kmap(pfn_to_page(p->shadow_pfn));
        *(uint32_t *)((char *)kaddr_shadow + (req->addr & ~PAGE_MASK)) = req->data;
        kunmap(pfn_to_page(p->shadow_pfn));
        kpm_tlbi_page(p->vaddr);
        pr_info("[RX] Multi-Track: Updated existing page at %llx.\n", p->vaddr);
        mmput(mm); put_task_struct(task);
        return 0;
    }

    /* 核心 2：如果是一个新页面，寻找一个空闲槽位 */
    for (i = 0; i < MAX_RX_PAGES; i++) {
        if (!g_rx_pages[i].active) {
            p = &g_rx_pages[i];
            break;
        }
    }
    if (!p) {
        pr_err("[RX] Error: MAX_RX_PAGES reached!\n");
        mmput(mm); put_task_struct(task);
        return -ENOMEM;
    }

    game_ptep = get_user_pte_safe(mm, req->addr & PAGE_MASK);
    if (!game_ptep) goto out;

    /* 分配并克隆物理页 */
    p->vaddr = req->addr & PAGE_MASK;
    orig_page = pte_page(*game_ptep);
    p->orig_pfn = page_to_pfn(orig_page);

    shadow_page = alloc_page(GFP_HIGHUSER | __GFP_ZERO);
    p->shadow_pfn = page_to_pfn(shadow_page);
    
    kaddr_orig = kmap(orig_page);
    kaddr_shadow = kmap(shadow_page);
    memcpy(kaddr_shadow, kaddr_orig, PAGE_SIZE);
    *(uint32_t *)((char *)kaddr_shadow + (req->addr & ~PAGE_MASK)) = req->data;
    kunmap(shadow_page);
    kunmap(orig_page);

    p->active = true;

    /* 埋下雷管：将 PTE 设为不可执行，强行迫使游戏执行时触发异常进入驱动 */
    entry = make_pte(p->orig_pfn, PTE_USER | PTE_RDONLY | PTE_UXN);
    *((volatile u64 *)game_ptep) = 0; 
    kpm_tlbi_page(p->vaddr);
    *((volatile u64 *)game_ptep) = entry;
    kpm_tlbi_page(p->vaddr);

    /* 初始化内核全局钩子 (仅执行一次) */
    if (!g_kernel_hooked) {
        pod_ptep = pte_offset_kernel((pmd_t *)k_init_mm, (unsigned long)my_escape_pod);
        if (pod_ptep) {
            pod_page = pte_page(*pod_ptep);
            pod_kaddr = kmap(pod_page);
            pod_offset = (unsigned long)my_escape_pod & ~PAGE_MASK;
            pod_ptr = (uint32_t *)((char *)pod_kaddr + pod_offset);
            orig_ptr = (uint32_t *)(k_do_fault & ~3UL);
            
            pod_ptr[0] = 0xD503249F;  // BTI J
            pod_ptr[1] = orig_ptr[1]; 
            pod_ptr[2] = orig_ptr[2]; 
            pod_ptr[3] = orig_ptr[3]; 
            pod_ptr[4] = orig_ptr[4]; 
            
            pod_ptr[5] = 0x58000050; 
            pod_ptr[6] = 0xD61F0200; 
            *((uint64_t *)&pod_ptr[7]) = k_do_fault + 20; 
            
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
        pr_info("[RX] KPM Standalone Engine V7 Online.\n");
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

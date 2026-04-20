#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/sched.h>
#include <linux/mm.h>
#include <linux/uaccess.h>
#include <linux/highmem.h>
#include <linux/vmalloc.h>
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
MODULE_DESCRIPTION("KPM Standalone R^X Engine V10 (Safe Vmap Patching)");

static unsigned long long k_do_fault = 0;
module_param(k_do_fault, ullong, 0444);

static unsigned long long k_exit_mmap = 0;
module_param(k_exit_mmap, ullong, 0444);

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
#ifndef PTE_USER
#define PTE_USER         (1ULL << 6)   
#endif
#ifndef PTE_RDONLY
#define PTE_RDONLY       (1ULL << 7)   
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

#define MAX_RX_PAGES 32
struct rx_page {
    uint64_t vaddr;
    uint64_t orig_pfn;
    uint64_t shadow_pfn;
    uint64_t orig_pte_val; 
    bool active;
};
static struct rx_page g_rx_pages[MAX_RX_PAGES];

static struct sock *nl_sk = NULL;
static struct mm_struct *g_game_mm = NULL;
static bool g_kernel_hooked = false;

static DEFINE_PER_CPU(int, g_in_hook);

/* 物理逃逸舱（预留足够空间供安全替换） */
__attribute__((naked)) void my_escape_pod(void) {
    asm volatile("nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n");
}
__attribute__((naked)) void my_exit_mmap_escape_pod(void) {
    asm volatile("nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n");
}

static inline void kpm_tlbi_page(unsigned long uaddr) {
    asm volatile(
        "dsb ishst\n"
        "tlbi vaale1is, %0\n"
        "dsb ish\n"
        "isb\n"
        : : "r"(uaddr >> 12) : "memory"
    );
}

/* --- 核心 1：安全的 Vmap 内存指令强制改写（绝不破坏内核 2MB 块映射） --- */
static int safe_vmap_patch(unsigned long target_vaddr, uint32_t *insns, int count) {
    u64 par;
    struct page *kpage;
    void *rw_addr;
    uint32_t *ptr;
    
    /* 使用底层 CPU 指令获取物理地址，100% 精准无误 */
    asm volatile("at s1e1r, %0" : : "r"(target_vaddr));
    asm volatile("isb");
    asm volatile("mrs %0, par_el1" : "=r"(par));
    if (par & 1) {
        pr_err("[RX] AT translation failed for %lx\n", target_vaddr);
        return -1;
    }
    
    kpage = pfn_to_page((par & 0x0000FFFFFFFFF000UL) >> PAGE_SHIFT);
    rw_addr = vmap(&kpage, 1, VM_MAP, PAGE_KERNEL);
    if (!rw_addr) {
        pr_err("[RX] vmap failed for %lx\n", target_vaddr);
        return -1;
    }
    
    ptr = (uint32_t *)((char *)rw_addr + (target_vaddr & ~PAGE_MASK));
    memcpy(ptr, insns, count * sizeof(uint32_t));
    
    vunmap(rw_addr);
    /* 全局刷新指令缓存，确保新指令生效 */
    asm volatile("ic ialluis\n dsb ish\n isb\n" ::: "memory");
    return 0;
}

/* --- 核心 2：完美克隆属性，保持设备内存特征不被破坏 --- */
static u64 build_shadow_pte(struct rx_page *p) {
    u64 entry = p->orig_pte_val;
    entry &= ~0x0000FFFFFFFFF000UL;
    entry |= (p->shadow_pfn << PAGE_SHIFT) & 0x0000FFFFFFFFF000UL;
    entry |= PTE_USER | PTE_RDONLY;
    entry &= ~PTE_UXN; 
    entry &= ~PTE_PXN; 
    return entry;
}

static u64 build_orig_pte(struct rx_page *p) {
    u64 entry = p->orig_pte_val;
    entry &= ~0x0000FFFFFFFFF000UL;
    entry |= (p->orig_pfn << PAGE_SHIFT) & 0x0000FFFFFFFFF000UL;
    entry |= PTE_USER | PTE_RDONLY;
    entry |= PTE_UXN; 
    entry |= PTE_PXN; 
    return entry;
}

static u64 build_restore_pte(struct rx_page *p) {
    return p->orig_pte_val;
}

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
    if ((pte_val(*(pte_t*)pmd) & 3) == 1) return NULL; 
    ptep = pte_offset_map(pmd, vaddr);
    return ptep;
}

/* --- 缺页分发器 --- */
int my_fault_dispatcher(unsigned long addr, unsigned int esr, struct pt_regs *regs) {
    unsigned int ec;
    pte_t *ptep;
    unsigned long flags;
    struct rx_page *p = NULL;
    int i;

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
        *((volatile u64 *)ptep) = 0; kpm_tlbi_page(p->vaddr);
        *((volatile u64 *)ptep) = build_shadow_pte(p); kpm_tlbi_page(p->vaddr);
        __this_cpu_write(g_in_hook, 0);
        local_irq_restore(flags);
        return 1;
    } else if (ec == EC_DATA_ABORT_L) {
        *((volatile u64 *)ptep) = 0; kpm_tlbi_page(p->vaddr);
        *((volatile u64 *)ptep) = build_orig_pte(p); kpm_tlbi_page(p->vaddr);
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
        "stp x0, x1, [sp, #-16]!\n" "stp x2, x3, [sp, #-16]!\n"
        "stp x4, x5, [sp, #-16]!\n" "stp x6, x7, [sp, #-16]!\n"
        "stp x8, x9, [sp, #-16]!\n" "stp x10, x11, [sp, #-16]!\n"
        "stp x12, x13, [sp, #-16]!\n" "stp x14, x15, [sp, #-16]!\n"
        "stp x16, x17, [sp, #-16]!\n" "stp x18, x19, [sp, #-16]!\n"
        "stp x29, x30, [sp, #-16]!\n"
        "bl my_fault_dispatcher\n"
        "cmp x0, #1\n"
        "b.eq .L_handled\n"
        "ldp x29, x30, [sp], #16\n" "ldp x18, x19, [sp], #16\n"
        "ldp x16, x17, [sp], #16\n" "ldp x14, x15, [sp], #16\n"
        "ldp x12, x13, [sp], #16\n" "ldp x10, x11, [sp], #16\n"
        "ldp x8, x9, [sp], #16\n" "ldp x6, x7, [sp], #16\n"
        "ldp x4, x5, [sp], #16\n" "ldp x2, x3, [sp], #16\n"
        "ldp x0, x1, [sp], #16\n"
        "ldr x16, =my_escape_pod\n" 
        "br x16\n"
        ".L_handled:\n"
        "ldp x29, x30, [sp], #16\n" "ldp x18, x19, [sp], #16\n"
        "ldp x16, x17, [sp], #16\n" "ldp x14, x15, [sp], #16\n"
        "ldp x12, x13, [sp], #16\n" "ldp x10, x11, [sp], #16\n"
        "ldp x8, x9, [sp], #16\n" "ldp x6, x7, [sp], #16\n"
        "ldp x4, x5, [sp], #16\n" "ldp x2, x3, [sp], #16\n"
        "ldp x0, x1, [sp], #16\n"
        "ret\n"
    );
}

/* 进程死亡自动清理管家 */
void my_exit_mmap_dispatcher(struct mm_struct *mm) {
    int i; pte_t *ptep;
    if (!mm || mm != g_game_mm) return;

    for (i = 0; i < MAX_RX_PAGES; i++) {
        if (g_rx_pages[i].active) {
            ptep = get_user_pte_safe(mm, g_rx_pages[i].vaddr);
            if (ptep) {
                *((volatile u64 *)ptep) = 0; kpm_tlbi_page(g_rx_pages[i].vaddr);
                *((volatile u64 *)ptep) = build_restore_pte(&g_rx_pages[i]); 
                kpm_tlbi_page(g_rx_pages[i].vaddr);
            }
            __free_page(pfn_to_page(g_rx_pages[i].shadow_pfn));
            g_rx_pages[i].active = false;
        }
    }
    g_game_mm = NULL;
    pr_info("[RX] Auto Teardown Done.\n");
}

__attribute__((naked)) void my_exit_mmap_trampoline(void) {
    asm volatile(
        "stp x0, x1, [sp, #-16]!\n" "stp x2, x3, [sp, #-16]!\n"
        "stp x4, x5, [sp, #-16]!\n" "stp x6, x7, [sp, #-16]!\n"
        "stp x8, x9, [sp, #-16]!\n" "stp x10, x11, [sp, #-16]!\n"
        "stp x12, x13, [sp, #-16]!\n" "stp x14, x15, [sp, #-16]!\n"
        "stp x16, x17, [sp, #-16]!\n" "stp x18, x19, [sp, #-16]!\n"
        "stp x29, x30, [sp, #-16]!\n"
        "bl my_exit_mmap_dispatcher\n"
        "ldp x29, x30, [sp], #16\n" "ldp x18, x19, [sp], #16\n"
        "ldp x16, x17, [sp], #16\n" "ldp x14, x15, [sp], #16\n"
        "ldp x12, x13, [sp], #16\n" "ldp x10, x11, [sp], #16\n"
        "ldp x8, x9, [sp], #16\n" "ldp x6, x7, [sp], #16\n"
        "ldp x4, x5, [sp], #16\n" "ldp x2, x3, [sp], #16\n"
        "ldp x0, x1, [sp], #16\n"
        "ldr x16, =my_exit_mmap_escape_pod\n" 
        "br x16\n"
    );
}

static int inject_and_setup_rx(struct rx_patch_req *req) {
    struct task_struct *task; struct mm_struct *mm;
    struct page *orig_page, *shadow_page;
    void *kaddr_orig, *kaddr_shadow;
    pte_t *game_ptep;
    uint32_t pod_insns[9];
    uint32_t hook_insns[4];
    uint32_t *orig_ptr;
    int i; struct rx_page *p = NULL;

    if (req->addr == 0) {
        if (g_game_mm) my_exit_mmap_dispatcher(g_game_mm);
        return 0;
    }

    if (!k_do_fault) return -EINVAL;

    rcu_read_lock();
    task = pid_task(find_vpid(req->pid), PIDTYPE_PID);
    if (task) get_task_struct(task);
    rcu_read_unlock();
    if (!task) return -ESRCH;

    mm = get_task_mm(task);
    if (!mm) { put_task_struct(task); return -EINVAL; }
    
    g_game_mm = mm;

    for (i = 0; i < MAX_RX_PAGES; i++) {
        if (g_rx_pages[i].active && g_rx_pages[i].vaddr == (req->addr & PAGE_MASK)) {
            p = &g_rx_pages[i]; break;
        }
    }

    if (p) {
        kaddr_shadow = kmap(pfn_to_page(p->shadow_pfn));
        *(uint32_t *)((char *)kaddr_shadow + (req->addr & ~PAGE_MASK)) = req->data;
        asm volatile("ic ialluis\n dsb ish\n isb\n" ::: "memory"); 
        kunmap(pfn_to_page(p->shadow_pfn));
        kpm_tlbi_page(p->vaddr);
        mmput(mm); put_task_struct(task);
        return 0;
    }

    for (i = 0; i < MAX_RX_PAGES; i++) {
        if (!g_rx_pages[i].active) { p = &g_rx_pages[i]; break; }
    }
    if (!p) { mmput(mm); put_task_struct(task); return -ENOMEM; }

    game_ptep = get_user_pte_safe(mm, req->addr & PAGE_MASK);
    if (!game_ptep) goto out;

    p->vaddr = req->addr & PAGE_MASK;
    p->orig_pte_val = pte_val(*game_ptep); 

    orig_page = pte_page(*game_ptep);
    p->orig_pfn = page_to_pfn(orig_page);

    shadow_page = alloc_page(GFP_HIGHUSER | __GFP_ZERO);
    p->shadow_pfn = page_to_pfn(shadow_page);
    
    kaddr_orig = kmap(orig_page);
    kaddr_shadow = kmap(shadow_page);
    memcpy(kaddr_shadow, kaddr_orig, PAGE_SIZE);
    *(uint32_t *)((char *)kaddr_shadow + (req->addr & ~PAGE_MASK)) = req->data;
    asm volatile("ic ialluis\n dsb ish\n isb\n" ::: "memory"); 
    kunmap(shadow_page); kunmap(orig_page);

    p->active = true;

    *((volatile u64 *)game_ptep) = 0; kpm_tlbi_page(p->vaddr);
    *((volatile u64 *)game_ptep) = build_orig_pte(p); kpm_tlbi_page(p->vaddr);

    if (!g_kernel_hooked) {
        /* Hook 1: 安全 vmap 挂载缺页异常 */
        orig_ptr = (uint32_t *)(k_do_fault & ~3UL);
        pod_insns[0] = 0xD503249F;  // BTI J
        pod_insns[1] = orig_ptr[1]; pod_insns[2] = orig_ptr[2]; 
        pod_insns[3] = orig_ptr[3]; pod_insns[4] = orig_ptr[4]; 
        pod_insns[5] = 0x58000050;  // LDR X16, #8
        pod_insns[6] = 0xD61F0200;  // BR X16
        *((uint64_t *)&pod_insns[7]) = k_do_fault + 20; 
        safe_vmap_patch((unsigned long)my_escape_pod, pod_insns, 9);
        
        hook_insns[0] = 0x58000050; // LDR X16, #8
        hook_insns[1] = 0xD61F0200; // BR X16
        *((uint64_t *)&hook_insns[2]) = (uint64_t)my_fault_trampoline;
        safe_vmap_patch(k_do_fault + 4, hook_insns, 4);

        /* Hook 2: 安全 vmap 挂载进程死亡回调 */
        if (k_exit_mmap) {
            orig_ptr = (uint32_t *)(k_exit_mmap & ~3UL);
            pod_insns[0] = 0xD503249F; 
            pod_insns[1] = orig_ptr[1]; pod_insns[2] = orig_ptr[2]; 
            pod_insns[3] = orig_ptr[3]; pod_insns[4] = orig_ptr[4]; 
            pod_insns[5] = 0x58000050; pod_insns[6] = 0xD61F0200; 
            *((uint64_t *)&pod_insns[7]) = k_exit_mmap + 20; 
            safe_vmap_patch((unsigned long)my_exit_mmap_escape_pod, pod_insns, 9);
            
            hook_insns[0] = 0x58000050; 
            hook_insns[1] = 0xD61F0200; 
            *((uint64_t *)&hook_insns[2]) = (uint64_t)my_exit_mmap_trampoline;
            safe_vmap_patch(k_exit_mmap + 4, hook_insns, 4);
        }
        g_kernel_hooked = true;
        pr_info("[RX] KPM V10 (Safe Vmap Patch) Online.\n");
    }

out:
    mmput(mm); put_task_struct(task);
    return 0;
}

static void nl_recv_msg(struct sk_buff *skb) {
    struct nlmsghdr *nlh; struct rx_patch_req *req;
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

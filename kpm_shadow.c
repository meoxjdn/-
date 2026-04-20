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
MODULE_DESCRIPTION("KPM-Derived Standalone R^X Engine");

static unsigned long long k_do_fault = 0;
module_param(k_do_fault, ullong, 0444);

static unsigned long long k_init_mm = 0;
module_param(k_init_mm, ullong, 0444);

#define NETLINK_WUWA 29 

/* --- 异常向量症状解析 (带防重定义护盾) --- */
#ifndef ESR_ELx_EC_SHIFT
#define ESR_ELx_EC_SHIFT    26
#endif
#ifndef EC_INSN_ABORT_L
#define EC_INSN_ABORT_L     0x20  
#endif
#ifndef EC_DATA_ABORT_L
#define EC_DATA_ABORT_L     0x24  
#endif

/* --- KPM 级别的 ARM64 PTE 魔法标志位 (带防重定义护盾) --- */
#ifndef PTE_VALID
#define PTE_VALID        (1ULL << 0)
#endif
#ifndef PTE_TYPE_PAGE
#define PTE_TYPE_PAGE    (3ULL << 0)
#endif
#ifndef PTE_USER
#define PTE_USER         (1ULL << 6)   // AP[1]
#endif
#ifndef PTE_RDONLY
#define PTE_RDONLY       (1ULL << 7)   // AP[2]
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
#ifndef PTE_GP_BIT
#define PTE_GP_BIT       (1ULL << 50)  // BTI 保护
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

/* 防并发套娃锁 */
static DEFINE_PER_CPU(int, g_in_hook);

uint8_t g_trampoline_escape_pod[32]; 

/* ---------------- KPM 级底层核心函数 ---------------- */

/* 狙击级 TLB 刷新：仅刷新目标虚拟地址，无损耗不死机 */
static inline void kpm_tlbi_page(unsigned long uaddr) {
    asm volatile(
        "dsb ishst\n"
        "tlbi vaale1is, %0\n"  /* 核心魔法：广播刷新所有 ASID 的指定 VA */
        "dsb ish\n"
        "isb\n"
        : : "r"(uaddr >> 12) : "memory"
    );
}

/* 构建完美 PTE 的核心工厂 */
static u64 make_pte(unsigned long pfn, u64 prot) {
    /* 注入必须的硬件标志位：AF(访问位), 共享, NG(非全局) */
    u64 entry = (pfn << PAGE_SHIFT) | prot | PTE_VALID | PTE_TYPE_PAGE | PTE_AF | (3ULL << 8) | PTE_NG;
    return entry;
}

/* 安全获取用户态 PTE，防止遇上 2MB 大页内存导致崩溃 */
static pte_t* get_user_pte_safe(struct mm_struct *mm, unsigned long vaddr) {
    pgd_t *pgd; p4d_t *p4d; pud_t *pud; pmd_t *pmd; pte_t *ptep;
    pgd = pgd_offset(mm, vaddr);
    if (pgd_none(*pgd) || pgd_bad(*pgd)) return NULL;
    p4d = p4d_offset(pgd, vaddr);
    if (p4d_none(*p4d) || p4d_bad(*p4d)) return NULL;
    pud = pud_offset(p4d, vaddr);
    if (pud_none(*pud) || pud_bad(*pud)) return NULL;
    pmd = pmd_offset(pud, vaddr);
    if (pmd_none(*pmd)) return NULL;
    
    /* 防崩溃核心：检测是否是 Huge Page (块映射) */
    if ((pte_val(*(pte_t*)pmd) & 3) == 1) {
        return NULL; // KPM 源码提示：遇到块映射必须先 split，这里简化处理直接拒绝
    }
    
    ptep = pte_offset_map(pmd, vaddr);
    return ptep;
}

/* ---------------- 缺页调度器 ---------------- */

int my_fault_dispatcher(unsigned long addr, unsigned int esr, struct pt_regs *regs) {
    /* 严格遵守 C90 标准，变量置顶 */
    unsigned int ec;
    pte_t *ptep;
    u64 entry;
    int *hook_flag;

    if (!g_target_vaddr || (addr & PAGE_MASK) != (g_target_vaddr & PAGE_MASK)) return 0; 

    hook_flag = this_cpu_ptr(&g_in_hook);
    if (*hook_flag) return 0;
    *hook_flag = 1;

    ec = esr >> ESR_ELx_EC_SHIFT;
    ptep = get_user_pte_safe(g_game_mm, g_target_vaddr);
    if (!ptep) {
        *hook_flag = 0;
        return 0;
    }

    if (ec == EC_INSN_ABORT_L) {
        /* 【KPM 影子页模式】：AP=0 (禁止读写), UXN=0 (允许执行) */
        entry = make_pte(g_shadow_pfn, 0); 
        *((volatile u64 *)ptep) = entry;
        kpm_tlbi_page(g_target_vaddr); 
        *hook_flag = 0;
        return 1;
    } else if (ec == EC_DATA_ABORT_L) {
        /* 【KPM 原版页模式】：AP=3 (允许读写), UXN=1 (禁止执行) */
        entry = make_pte(g_orig_pfn, PTE_USER | PTE_RDONLY | PTE_UXN);
        *((volatile u64 *)ptep) = entry;
        kpm_tlbi_page(g_target_vaddr); 
        *hook_flag = 0;
        return 1;
    }
    
    *hook_flag = 0;
    return 0;
}

/* ---------------- 物理跳板 (修复返回逻辑) ---------------- */

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
        "ret\n" /* 安全返回 */
    );
}

/* ---------------- 致命注射与引擎初始化 ---------------- */

static int inject_and_setup_rx(struct rx_patch_req *req) {
    /* 严格遵守 C90 标准，所有变量置顶声明 */
    struct task_struct *task;
    struct mm_struct *mm;
    struct page *orig_page, *shadow_page, *new_kpage;
    void *kaddr_orig, *kaddr_shadow, *kaddr_new_kernel;
    pte_t *game_ptep, *kernel_ptep;
    unsigned long flags, offset;
    uint32_t *patch_addr, *escape_tail;
    u64 entry;
    u64 raw_kpte;

    /* 清理还原逻辑 */
    if (req->addr == 0) {
        if (g_target_vaddr && g_game_mm) {
            game_ptep = get_user_pte_safe(g_game_mm, g_target_vaddr);
            if (game_ptep) {
                entry = make_pte(g_orig_pfn, PTE_USER | PTE_UXN); // 还原正常状态
                *((volatile u64 *)game_ptep) = entry;
                kpm_tlbi_page(g_target_vaddr);
            }
            g_target_vaddr = 0;
            pr_info("[RX] KPM Mode Cleaned up.\n");
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

    /* 初始化触发雷管：剥夺执行权限，使其立刻触发异常 */
    entry = make_pte(g_orig_pfn, PTE_USER | PTE_RDONLY | PTE_UXN);
    *((volatile u64 *)game_ptep) = entry;
    kpm_tlbi_page(g_target_vaddr);

    if (!g_kernel_hooked) {
        kernel_ptep = pte_offset_kernel((pmd_t *)k_init_mm, k_do_fault); 
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

        /* Bypass PAC/BTI：从第4个字节开始跳，保留原函数的头部签名 */
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
        pr_info("[RX] KPM Standalone Engine Online.\n");
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

// SPDX-License-Identifier: GPL-2.0
/*
 * KPM Standalone R^X Engine V13
 *
 * 相对 V12 的修复：
 *   [FIX-T] g_game_mm 改为真正的弱引用语义：
 *           存储时不持有 mm_users 引用（注入完成后立刻 mmput）。
 *           读取时通过 mmget_not_zero() 原子升级为强引用，
 *           操作完成后立刻 mmput，绝不长期持有。
 *           彻底消除 mm_users 泄漏导致的僵尸进程问题。
 *
 *   [FIX-U] my_exit_mmap_dispatcher 的 Phase 2 不再写回 PTE：
 *           exit_mmap 调用时页表正在被内核销毁，写回无意义且危险。
 *           Phase 2 仅释放 shadow page 物理内存，PTE 恢复由内核接管。
 *
 *   [FIX-V] inject_and_setup_rx 进程切换清理逻辑重构：
 *           不在持锁/出锁边界反复横跳调用 dispatcher，
 *           改为取出旧 mm 指针后在锁外单次调用，消除重入风险。
 *
 *   [FIX-W] my_fault_dispatcher 读取 g_game_mm 时通过
 *           mmget_not_zero() 升级强引用，用完立刻释放，
 *           消除并发 exit_mmap 导致的 mm_struct UAF。
 */

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
#include <linux/spinlock.h>
#include <linux/workqueue.h>
#include <linux/slab.h>
#include <linux/bug.h>
#include <linux/rcupdate.h>
#include <linux/sched/mm.h>   /* mmget_not_zero, mmput */

MODULE_LICENSE("GPL");
MODULE_AUTHOR("RX_Engine");
MODULE_DESCRIPTION("KPM Standalone R^X Engine V13");

/* -----------------------------------------------------------------------
 * 模块参数
 * ----------------------------------------------------------------------- */
static unsigned long long k_do_fault  = 0;
module_param(k_do_fault,  ullong, 0444);

static unsigned long long k_exit_mmap = 0;
module_param(k_exit_mmap, ullong, 0444);

/* -----------------------------------------------------------------------
 * 常量 & 宏
 * ----------------------------------------------------------------------- */
#define NETLINK_WUWA        29
#define MAX_RX_PAGES        32
#define ESCAPE_POD_SLOTS    32
#define ESCAPE_POD_BYTES    (ESCAPE_POD_SLOTS * 4)
#define MAX_EXPAND_PER_INSN 5
#define HOOK_PROLOGUE_INSNS 4

static_assert(ESCAPE_POD_SLOTS == 32,
    "ESCAPE_POD_SLOTS must match nop count in escape pods");

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
#define PTE_USER            (1ULL << 6)
#endif
#ifndef PTE_RDONLY
#define PTE_RDONLY          (1ULL << 7)
#endif
#ifndef PTE_AF
#define PTE_AF              (1ULL << 10)
#endif
#ifndef PTE_NG
#define PTE_NG              (1ULL << 11)
#endif
#ifndef PTE_PXN
#define PTE_PXN             (1ULL << 53)
#endif
#ifndef PTE_UXN
#define PTE_UXN             (1ULL << 54)
#endif

/* -----------------------------------------------------------------------
 * 数据结构
 * ----------------------------------------------------------------------- */
struct rx_patch_req {
    pid_t    pid;
    uint64_t addr;
    uint32_t data;
};

struct rx_page {
    uint64_t vaddr;
    uint64_t orig_pfn;
    uint64_t shadow_pfn;
    uint64_t orig_pte_val;
    bool     active;
};

struct hook_site {
    unsigned long addr;
    uint32_t      orig_insns[HOOK_PROLOGUE_INSNS];
    bool          installed;
};

/* -----------------------------------------------------------------------
 * 全局状态
 *
 * [FIX-T] g_game_mm 是弱引用指针：
 *   - 写入：inject_and_setup_rx 在 mmput 之前写入，mmput 之后指针仍有效
 *           但我们不依赖它的 mm_users > 0，只用它做身份标识。
 *   - 读取：必须通过 mmget_not_zero() 尝试升级，失败说明进程已在消亡，
 *           直接跳过操作。
 *   - 清空：由 my_exit_mmap_dispatcher（exit_mmap hook）负责，
 *           此时 mm_users 正在归零，是清空的最后时机。
 * ----------------------------------------------------------------------- */
static struct rx_page    g_rx_pages[MAX_RX_PAGES];
static DEFINE_SPINLOCK(g_rx_lock);
static struct sock      *nl_sk           = NULL;

/*
 * 弱引用：不持有 mm_users，仅作为"上次注入的目标"标识。
 * 所有读取路径必须通过 mmget_not_zero() 升级后才能解引用。
 */
static struct mm_struct *g_game_mm       = NULL;
static bool              g_kernel_hooked = false;
static struct hook_site  g_hook_fault;
static struct hook_site  g_hook_exit_mmap;

struct rx_work_item {
    struct work_struct  work;
    struct rx_patch_req req;
};
static struct workqueue_struct *g_rx_wq = NULL;

static DEFINE_PER_CPU(int, g_in_hook);

/* -----------------------------------------------------------------------
 * 前向声明
 * ----------------------------------------------------------------------- */
static int arm64_relocate_insns(uint32_t *dst, unsigned long dst_pc,
                                const uint32_t *src, unsigned long src_pc,
                                int src_count);

/* -----------------------------------------------------------------------
 * 逃逸舱
 * ----------------------------------------------------------------------- */
__attribute__((naked)) void my_escape_pod(void)
{
    asm volatile(
        "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n"
        "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n"
        "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n"
        "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n"
    );
}

__attribute__((naked)) void my_exit_mmap_escape_pod(void)
{
    asm volatile(
        "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n"
        "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n"
        "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n"
        "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n"
    );
}

/* -----------------------------------------------------------------------
 * TLB 失效
 * ----------------------------------------------------------------------- */
static inline void kpm_tlbi_page(unsigned long uaddr)
{
    asm volatile(
        "dsb ishst\n"
        "tlbi vaale1is, %0\n"
        "dsb ish\n"
        "isb\n"
        : : "r"(uaddr >> 12) : "memory"
    );
}

/* -----------------------------------------------------------------------
 * safe_vmap_patch（FIX-F：at s1e0r）
 * ----------------------------------------------------------------------- */
static int safe_vmap_patch(unsigned long target_vaddr,
                           uint32_t *insns, int count)
{
    u64         par;
    struct page *kpage;
    void        *rw_addr;
    uint32_t    *ptr;

    asm volatile("at s1e0r, %0" : : "r"(target_vaddr));
    asm volatile("isb");
    asm volatile("mrs %0, par_el1" : "=r"(par));
    if (par & 1) {
        pr_err("[RX] AT s1e0r failed for %lx (PAR=%llx)\n",
               target_vaddr, par);
        return -1;
    }
    kpage   = pfn_to_page((par & 0x0000FFFFFFFFF000UL) >> PAGE_SHIFT);
    rw_addr = vmap(&kpage, 1, VM_MAP, PAGE_KERNEL);
    if (!rw_addr) {
        pr_err("[RX] vmap failed for %lx\n", target_vaddr);
        return -1;
    }
    ptr = (uint32_t *)((char *)rw_addr + (target_vaddr & ~PAGE_MASK));
    memcpy(ptr, insns, count * sizeof(uint32_t));
    vunmap(rw_addr);
    asm volatile("ic ialluis\n dsb ish\n isb\n" ::: "memory");
    return 0;
}

/* -----------------------------------------------------------------------
 * PTE 构造（FIX-C）
 * ----------------------------------------------------------------------- */
#define PTE_PFN_MASK     0x0000FFFFFFFFF000UL
#define PTE_INHERIT_BITS (PTE_AF | PTE_NG)

static u64 build_shadow_pte(struct rx_page *p)
{
    u64 entry = p->orig_pte_val;
    entry &= ~PTE_PFN_MASK;
    entry |= (p->shadow_pfn << PAGE_SHIFT) & PTE_PFN_MASK;
    entry |= PTE_USER | PTE_RDONLY;
    entry &= ~PTE_UXN;
    entry &= ~PTE_PXN;
    entry |= (p->orig_pte_val & PTE_INHERIT_BITS);
    return entry;
}

static u64 build_orig_pte(struct rx_page *p)
{
    u64 entry = p->orig_pte_val;
    entry &= ~PTE_PFN_MASK;
    entry |= (p->orig_pfn << PAGE_SHIFT) & PTE_PFN_MASK;
    entry |= PTE_USER | PTE_RDONLY;
    entry |= PTE_UXN | PTE_PXN;
    entry |= (p->orig_pte_val & PTE_INHERIT_BITS);
    return entry;
}

static u64 build_restore_pte(struct rx_page *p)
{
    return p->orig_pte_val;
}

/* -----------------------------------------------------------------------
 * 页表遍历（FIX-A）
 * ----------------------------------------------------------------------- */
static pte_t *get_user_pte_and_pmd(struct mm_struct *mm,
                                   unsigned long vaddr,
                                   pmd_t **out_pmd)
{
    pgd_t *pgd; p4d_t *p4d; pud_t *pud; pmd_t *pmd; pte_t *ptep;

    if (!mm) return NULL;
    pgd = pgd_offset(mm, vaddr);
    if (pgd_none(*pgd) || pgd_bad(*pgd))    return NULL;
    p4d = p4d_offset(pgd, vaddr);
    if (p4d_none(*p4d) || p4d_bad(*p4d))    return NULL;
    pud = pud_offset(p4d, vaddr);
    if (pud_none(*pud) || pud_bad(*pud))     return NULL;
    pmd = pmd_offset(pud, vaddr);
    if (pmd_none(*pmd))                      return NULL;
    if ((pte_val(*(pte_t *)pmd) & 3) == 1)  return NULL;
    ptep = pte_offset_kernel(pmd, vaddr);
    if (out_pmd) *out_pmd = pmd;
    return ptep;
}

/* -----------------------------------------------------------------------
 * PTE 写入（FIX-A/D/O：在 g_rx_lock 之外调用）
 * ----------------------------------------------------------------------- */
static void pte_write_locked(struct mm_struct *mm,
                             unsigned long vaddr,
                             pmd_t *pmd,
                             pte_t *ptep,
                             u64 new_val)
{
    spinlock_t *ptl = pte_lockptr(mm, pmd);
    spin_lock(ptl);
    WRITE_ONCE(*((u64 *)ptep), new_val);
    kpm_tlbi_page(vaddr);
    spin_unlock(ptl);
}

/* -----------------------------------------------------------------------
 * 缺页分发器
 *
 * [FIX-W] 通过 mmget_not_zero() 安全升级 g_game_mm 弱引用：
 *   1. 持 g_rx_lock 读取 g_game_mm 指针
 *   2. 立刻调用 mmget_not_zero() 尝试原子递增 mm_users
 *   3. 成功：得到强引用，出锁后可安全操作
 *   4. 失败：进程正在消亡，mm_struct 即将释放，直接返回
 *   5. 操作完成后立刻 mmput() 归还引用
 *
 * 为什么要持锁再 mmget_not_zero：
 *   - 必须在持锁状态下读取指针并立刻升级，防止读指针和升级之间
 *     另一个核心将 g_game_mm 置 NULL 并释放 mm_struct。
 *   - mmget_not_zero 是原子操作，持锁状态下调用完全安全。
 * ----------------------------------------------------------------------- */
int my_fault_dispatcher(unsigned long addr, unsigned int esr,
                        struct pt_regs *regs)
{
    unsigned int      ec;
    pte_t            *ptep;
    pmd_t            *pmd;
    unsigned long     flags;
    struct rx_page   *p  = NULL;
    struct mm_struct *mm = NULL;
    int               i;

    spin_lock_irqsave(&g_rx_lock, flags);

    if (!g_game_mm) {
        spin_unlock_irqrestore(&g_rx_lock, flags);
        return 0;
    }

    /* [FIX-W] 原子升级弱引用为强引用 */
    if (!mmget_not_zero(g_game_mm)) {
        /*
         * mm_users 已经是 0，进程正在消亡。
         * exit_mmap hook 会（或已经）清理，我们什么都不用做。
         */
        spin_unlock_irqrestore(&g_rx_lock, flags);
        return 0;
    }
    mm = g_game_mm; /* 现在持有强引用，mm_struct 不会消失 */

    for (i = 0; i < MAX_RX_PAGES; i++) {
        if (g_rx_pages[i].active &&
            (addr & PAGE_MASK) == g_rx_pages[i].vaddr) {
            p = &g_rx_pages[i];
            break;
        }
    }

    if (!p) {
        spin_unlock_irqrestore(&g_rx_lock, flags);
        mmput(mm); /* [FIX-W] 归还强引用 */
        return 0;
    }

    if (__this_cpu_read(g_in_hook)) {
        spin_unlock_irqrestore(&g_rx_lock, flags);
        mmput(mm);
        return 0;
    }
    __this_cpu_write(g_in_hook, 1);

    /*
     * 出锁后操作：此时持有 mm 强引用，mm_struct 安全。
     * 注意：ptep 在出锁后可能因进程退出而无效，
     * 但我们已经持有强引用，exit_mmap 必须等我们 mmput 后才能完成，
     * 所以页表在这段时间内是稳定的。
     */
    spin_unlock_irqrestore(&g_rx_lock, flags);

    ptep = get_user_pte_and_pmd(mm, p->vaddr, &pmd);
    if (!ptep) {
        __this_cpu_write(g_in_hook, 0);
        mmput(mm);
        return 0;
    }

    ec = esr >> ESR_ELx_EC_SHIFT;

    if (ec == EC_INSN_ABORT_L) {
        pte_write_locked(mm, p->vaddr, pmd, ptep, build_shadow_pte(p));
        __this_cpu_write(g_in_hook, 0);
        mmput(mm); /* [FIX-W] 归还 */
        return 1;
    } else if (ec == EC_DATA_ABORT_L) {
        pte_write_locked(mm, p->vaddr, pmd, ptep, build_orig_pte(p));
        __this_cpu_write(g_in_hook, 0);
        mmput(mm);
        return 1;
    }

    __this_cpu_write(g_in_hook, 0);
    mmput(mm);
    return 0;
}

/* -----------------------------------------------------------------------
 * 缺页 trampoline（FIX-G/S）
 * ----------------------------------------------------------------------- */
__attribute__((naked)) void my_fault_trampoline(void)
{
    asm volatile(
        "stp x0,  x1,  [sp, #-16]!\n"
        "stp x2,  x3,  [sp, #-16]!\n"
        "stp x4,  x5,  [sp, #-16]!\n"
        "stp x6,  x7,  [sp, #-16]!\n"
        "stp x8,  x9,  [sp, #-16]!\n"
        "stp x10, x11, [sp, #-16]!\n"
        "stp x12, x13, [sp, #-16]!\n"
        "stp x14, x15, [sp, #-16]!\n"
        "stp x16, x17, [sp, #-16]!\n"
        "stp x18, x19, [sp, #-16]!\n"
        "stp x20, x21, [sp, #-16]!\n"
        "stp x22, x23, [sp, #-16]!\n"
        "stp x24, x25, [sp, #-16]!\n"
        "stp x26, x27, [sp, #-16]!\n"
        "stp x28, x29, [sp, #-16]!\n"
        "str x30,       [sp, #-8]!\n"
        "bl my_fault_dispatcher\n"
        "cmp x0, #1\n"
        "b.eq .L_fault_handled\n"
        "ldr x30,       [sp], #8\n"
        "ldp x28, x29, [sp], #16\n"
        "ldp x26, x27, [sp], #16\n"
        "ldp x24, x25, [sp], #16\n"
        "ldp x22, x23, [sp], #16\n"
        "ldp x20, x21, [sp], #16\n"
        "ldp x18, x19, [sp], #16\n"
        "ldp x16, x17, [sp], #16\n"
        "ldp x14, x15, [sp], #16\n"
        "ldp x12, x13, [sp], #16\n"
        "ldp x10, x11, [sp], #16\n"
        "ldp x8,  x9,  [sp], #16\n"
        "ldp x6,  x7,  [sp], #16\n"
        "ldp x4,  x5,  [sp], #16\n"
        "ldp x2,  x3,  [sp], #16\n"
        "ldp x0,  x1,  [sp], #16\n"
        "ldr x16, =my_escape_pod\n"
        "br  x16\n"
        ".L_fault_handled:\n"
        "ldr x30,       [sp], #8\n"
        "ldp x28, x29, [sp], #16\n"
        "ldp x26, x27, [sp], #16\n"
        "ldp x24, x25, [sp], #16\n"
        "ldp x22, x23, [sp], #16\n"
        "ldp x20, x21, [sp], #16\n"
        "ldp x18, x19, [sp], #16\n"
        "ldp x16, x17, [sp], #16\n"
        "ldp x14, x15, [sp], #16\n"
        "ldp x12, x13, [sp], #16\n"
        "ldp x10, x11, [sp], #16\n"
        "ldp x8,  x9,  [sp], #16\n"
        "ldp x6,  x7,  [sp], #16\n"
        "ldp x4,  x5,  [sp], #16\n"
        "ldp x2,  x3,  [sp], #16\n"
        "ldp x0,  x1,  [sp], #16\n"
        "ret\n"
    );
}

/* -----------------------------------------------------------------------
 * 进程退出清理
 *
 * [FIX-T] 不调用 mmput：此函数由 exit_mmap hook 触发，
 *         调用时 mm_users 正在归零，我们没有持有引用，不需要释放。
 *
 * [FIX-U] Phase 2 不写回 PTE：
 *         exit_mmap 调用时页表正在被内核销毁，写回 PTE 无意义且危险。
 *         Phase 2 仅做 shadow page 物理内存释放。
 *         PTE 恢复由内核的 unmap_vmas() 流程接管。
 *
 * [FIX-V] 由 exit_mmap hook 直接传入 mm，不存在指针有效性问题。
 * ----------------------------------------------------------------------- */
struct rx_cleanup_entry {
    uint64_t shadow_pfn;
};

void my_exit_mmap_dispatcher(struct mm_struct *mm)
{
    struct rx_cleanup_entry entries[MAX_RX_PAGES];
    int    count = 0, i;
    unsigned long flags;

    if (!mm) return;

    /* Phase 1：持锁收集 shadow_pfn，清空元数据 */
    spin_lock_irqsave(&g_rx_lock, flags);

    if (mm != g_game_mm) {
        spin_unlock_irqrestore(&g_rx_lock, flags);
        return;
    }

    for (i = 0; i < MAX_RX_PAGES; i++) {
        if (g_rx_pages[i].active) {
            entries[count].shadow_pfn = g_rx_pages[i].shadow_pfn;
            count++;
            g_rx_pages[i].active = false;
        }
    }

    /*
     * [FIX-T] 绝不调用 mmput：
     *   我们从未持有这个 mm 的 mm_users 引用（注入时立刻 mmput），
     *   所以这里只需要清空弱引用指针即可。
     */
    g_game_mm = NULL;

    spin_unlock_irqrestore(&g_rx_lock, flags);

    /*
     * Phase 2：出锁释放 shadow page 物理内存。
     *
     * [FIX-U] 不写回 PTE：
     *   exit_mmap 由内核调用时，unmap_vmas() 已经或即将清除所有用户 PTE，
     *   我们写回的值会被立刻覆盖，且写入过程中 pmd 指针可能已经无效。
     *   只需释放 shadow page 物理内存，防止内存泄漏。
     */
    for (i = 0; i < count; i++)
        __free_page(pfn_to_page(entries[i].shadow_pfn));

    pr_info("[RX] Auto Teardown Done (%d shadow pages freed).\n", count);
}

/* -----------------------------------------------------------------------
 * exit_mmap trampoline（FIX-G）
 * ----------------------------------------------------------------------- */
__attribute__((naked)) void my_exit_mmap_trampoline(void)
{
    asm volatile(
        "stp x0,  x1,  [sp, #-16]!\n"
        "stp x2,  x3,  [sp, #-16]!\n"
        "stp x4,  x5,  [sp, #-16]!\n"
        "stp x6,  x7,  [sp, #-16]!\n"
        "stp x8,  x9,  [sp, #-16]!\n"
        "stp x10, x11, [sp, #-16]!\n"
        "stp x12, x13, [sp, #-16]!\n"
        "stp x14, x15, [sp, #-16]!\n"
        "stp x16, x17, [sp, #-16]!\n"
        "stp x18, x19, [sp, #-16]!\n"
        "stp x20, x21, [sp, #-16]!\n"
        "stp x22, x23, [sp, #-16]!\n"
        "stp x24, x25, [sp, #-16]!\n"
        "stp x26, x27, [sp, #-16]!\n"
        "stp x28, x29, [sp, #-16]!\n"
        "str x30,       [sp, #-8]!\n"
        "bl  my_exit_mmap_dispatcher\n"
        "ldr x30,       [sp], #8\n"
        "ldp x28, x29, [sp], #16\n"
        "ldp x26, x27, [sp], #16\n"
        "ldp x24, x25, [sp], #16\n"
        "ldp x22, x23, [sp], #16\n"
        "ldp x20, x21, [sp], #16\n"
        "ldp x18, x19, [sp], #16\n"
        "ldp x16, x17, [sp], #16\n"
        "ldp x14, x15, [sp], #16\n"
        "ldp x12, x13, [sp], #16\n"
        "ldp x10, x11, [sp], #16\n"
        "ldp x8,  x9,  [sp], #16\n"
        "ldp x6,  x7,  [sp], #16\n"
        "ldp x4,  x5,  [sp], #16\n"
        "ldp x2,  x3,  [sp], #16\n"
        "ldp x0,  x1,  [sp], #16\n"
        "ldr x16, =my_exit_mmap_escape_pod\n"
        "br  x16\n"
    );
}

/* -----------------------------------------------------------------------
 * ARM64 指令重定位引擎（FIX-B/I/J/Q）
 * ----------------------------------------------------------------------- */
static int arm64_relocate_insns(uint32_t *dst, unsigned long dst_pc,
                                const uint32_t *src, unsigned long src_pc,
                                int src_count)
{
    int si, di = 0;
    const int dst_slots = ESCAPE_POD_SLOTS - 1 - 4;

    for (si = 0; si < src_count; si++) {
        uint32_t      insn       = src[si];
        unsigned long cur_src_pc = src_pc + si * 4;
        unsigned long cur_dst_pc = dst_pc + di * 4;

        if (di + MAX_EXPAND_PER_INSN > dst_slots) {
            pr_err("[RX] reloc overflow si=%d di=%d\n", si, di);
            return -1;
        }

        /* B / BL */
        if ((insn & 0x7C000000) == 0x14000000) {
            int64_t       off26  = (int64_t)((int32_t)(insn << 6) >> 6);
            unsigned long target = cur_src_pc + (unsigned long)(off26 * 4);
            int64_t       noff   = ((int64_t)(target - cur_dst_pc)) / 4;
            int           is_bl  = (insn >> 31) & 1;
            if (noff >= -(1<<25) && noff < (1<<25)) {
                dst[di++] = (insn & 0xFC000000) | ((uint32_t)noff & 0x03FFFFFF);
            } else if (is_bl) {
                dst[di++] = 0xD2800010|(((target>> 0)&0xFFFF)<<5);
                dst[di++] = 0xF2A00010|(((target>>16)&0xFFFF)<<5);
                dst[di++] = 0xF2C00010|(((target>>32)&0xFFFF)<<5);
                dst[di++] = 0xF2E00010|(((target>>48)&0xFFFF)<<5);
                dst[di++] = 0xD63F0200;
            } else {
                dst[di++] = 0x58000050;
                dst[di++] = 0xD61F0200;
                *((uint64_t*)&dst[di]) = target; di += 2;
            }
            continue;
        }

        /* B.cond */
        if ((insn & 0xFF000010) == 0x54000000) {
            int64_t       off19  = (int64_t)((int32_t)((insn>>5)<<13)>>13);
            unsigned long target = cur_src_pc + (unsigned long)(off19*4);
            int64_t       noff   = ((int64_t)(target - cur_dst_pc)) / 4;
            if (noff >= -(1<<18) && noff < (1<<18)) {
                dst[di++] = (insn & 0xFF00001F)|(((uint32_t)noff&0x7FFFF)<<5);
            } else {
                dst[di++] = 0x54000000|((insn&0xF)^1)|(4<<5);
                dst[di++] = 0x58000050;
                dst[di++] = 0xD61F0200;
                *((uint64_t*)&dst[di]) = target; di += 2;
            }
            continue;
        }

        /* CBZ / CBNZ */
        if ((insn & 0x7E000000) == 0x34000000) {
            int64_t       off19  = (int64_t)((int32_t)((insn>>5)<<13)>>13);
            unsigned long target = cur_src_pc + (unsigned long)(off19*4);
            int64_t       noff   = ((int64_t)(target - cur_dst_pc)) / 4;
            if (noff >= -(1<<18) && noff < (1<<18)) {
                dst[di++] = (insn & 0xFF00001F)|(((uint32_t)noff&0x7FFFF)<<5);
            } else {
                uint32_t sf=(insn>>31), opc=(insn>>24)&1, Rt=insn&0x1F;
                dst[di++] = (sf<<31)|((opc^1)<<24)|0x34000000|(4<<5)|Rt;
                dst[di++] = 0x58000050;
                dst[di++] = 0xD61F0200;
                *((uint64_t*)&dst[di]) = target; di += 2;
            }
            continue;
        }

        /* TBZ / TBNZ */
        if ((insn & 0x7E000000) == 0x36000000) {
            int64_t       off14  = (int64_t)((int32_t)((insn>>5)<<18)>>18);
            unsigned long target = cur_src_pc + (unsigned long)(off14*4);
            int64_t       noff   = ((int64_t)(target - cur_dst_pc)) / 4;
            if (noff >= -(1<<13) && noff < (1<<13)) {
                dst[di++] = (insn & 0xFFF8001F)|(((uint32_t)noff&0x3FFF)<<5);
            } else {
                uint32_t opc=(insn>>24)&1, Rt=insn&0x1F;
                uint32_t bit=((insn>>31)<<5)|((insn>>19)&0x1F);
                dst[di++] = ((bit>>5)<<31)|((opc^1)<<24)|0x36000000|
                            (4<<5)|((bit&0x1F)<<19)|Rt;
                dst[di++] = 0x58000050;
                dst[di++] = 0xD61F0200;
                *((uint64_t*)&dst[di]) = target; di += 2;
            }
            continue;
        }

        /* ADR */
        if ((insn & 0x9F000000) == 0x10000000) {
            uint32_t Rd = insn & 0x1F;
            int64_t immhi=(int32_t)((insn>>5)<<14)>>14, immlo=(insn>>29)&3;
            unsigned long target = cur_src_pc+(unsigned long)((immhi<<2)|immlo);
            dst[di++] = 0xD2800000|Rd|(((target>> 0)&0xFFFF)<<5);
            dst[di++] = 0xF2A00000|Rd|(((target>>16)&0xFFFF)<<5);
            dst[di++] = 0xF2C00000|Rd|(((target>>32)&0xFFFF)<<5);
            dst[di++] = 0xF2E00000|Rd|(((target>>48)&0xFFFF)<<5);
            continue;
        }

        /* ADRP */
        if ((insn & 0x9F000000) == 0x90000000) {
            uint32_t Rd = insn & 0x1F;
            int64_t immhi=(int32_t)((insn>>5)<<14)>>14, immlo=(insn>>29)&3;
            unsigned long target=(cur_src_pc&~0xFFFUL)+(unsigned long)(((immhi<<2)|immlo)<<12);
            dst[di++] = 0xD2800000|Rd|(((target>> 0)&0xFFFF)<<5);
            dst[di++] = 0xF2A00000|Rd|(((target>>16)&0xFFFF)<<5);
            dst[di++] = 0xF2C00000|Rd|(((target>>32)&0xFFFF)<<5);
            dst[di++] = 0xF2E00000|Rd|(((target>>48)&0xFFFF)<<5);
            continue;
        }

        /* LDR literal */
        if ((insn & 0x3B000000) == 0x18000000) {
            uint32_t opc=insn>>30, Rt=insn&0x1F;
            int64_t  off19=(int64_t)((int32_t)((insn>>5)<<13)>>13);
            unsigned long target=cur_src_pc+(unsigned long)(off19*4);
            dst[di++] = 0xD2800010|(((target>> 0)&0xFFFF)<<5);
            dst[di++] = 0xF2A00010|(((target>>16)&0xFFFF)<<5);
            dst[di++] = 0xF2C00010|(((target>>32)&0xFFFF)<<5);
            dst[di++] = 0xF2E00010|(((target>>48)&0xFFFF)<<5);
            switch(opc){
            case 0: dst[di++]=0xB9400200|Rt; break;
            case 1: dst[di++]=0xF9400200|Rt; break;
            case 2: dst[di++]=0xB9800200|Rt; break;
            case 3: dst[di++]=0x3DC00200|Rt; break;
            }
            continue;
        }

        dst[di++] = insn;
    }
    return di;
}

/* -----------------------------------------------------------------------
 * 安全 Unhook（FIX-M）
 * ----------------------------------------------------------------------- */
static void do_safe_unhook(struct hook_site *site)
{
    if (!site->installed) return;
    pr_info("[RX] Unhooking %lx\n", site->addr);
    safe_vmap_patch(site->addr, site->orig_insns, HOOK_PROLOGUE_INSNS);
    site->installed = false;
    synchronize_rcu();
    pr_info("[RX] Unhook done for %lx\n", site->addr);
}

/* -----------------------------------------------------------------------
 * inject_and_setup_rx
 *
 * [FIX-T] 核心变更：注入完成后立刻 mmput，绝不长期持有 mm_users。
 * [FIX-V] 进程切换：取出旧 mm 后出锁，锁外单次调用 dispatcher 清理。
 * ----------------------------------------------------------------------- */
static int inject_and_setup_rx(struct rx_patch_req *req)
{
    struct task_struct *task;
    struct mm_struct   *mm, *old_mm = NULL;
    struct page        *orig_page, *shadow_page;
    void               *kaddr_orig, *kaddr_shadow;
    pte_t              *game_ptep;
    pmd_t              *game_pmd;
    uint32_t            hook_insns[HOOK_PROLOGUE_INSNS];
    int                 i;
    struct rx_page     *p = NULL;
    unsigned long       flags;
    bool                need_write_pte   = false;
    u64                 pte_val_to_write = 0;

    if (req->addr == 0) {
        spin_lock_irqsave(&g_rx_lock, flags);
        old_mm = g_game_mm;
        g_game_mm = NULL; /* 先置空，防止 dispatcher 并发操作 */
        spin_unlock_irqrestore(&g_rx_lock, flags);
        if (old_mm)
            my_exit_mmap_dispatcher(old_mm);
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

    /*
     * [FIX-V] 进程切换检测：
     *   取出 old_mm 后立刻出锁，在锁外调用 dispatcher 清理旧实例。
     *   不在持锁/出锁边界反复横跳，避免状态不一致和重入。
     */
    spin_lock_irqsave(&g_rx_lock, flags);
    if (g_game_mm && g_game_mm != mm) {
        old_mm    = g_game_mm;
        g_game_mm = NULL; /* 提前置空，防止并发 dispatcher 操作旧实例 */
    }
    spin_unlock_irqrestore(&g_rx_lock, flags);

    /* 锁外清理旧实例（my_exit_mmap_dispatcher 内部会再次加锁，
     * 但因为我们已经将 g_game_mm 置 NULL，它会发现 mm != g_game_mm
     * 并立刻返回——这里直接手动调用清理逻辑更清晰） */
    if (old_mm) {
        /* 直接清理旧实例的 shadow pages，不依赖 dispatcher 的身份判断 */
        unsigned long f2;
        spin_lock_irqsave(&g_rx_lock, f2);
        for (i = 0; i < MAX_RX_PAGES; i++) {
            if (g_rx_pages[i].active) {
                __free_page(pfn_to_page(g_rx_pages[i].shadow_pfn));
                g_rx_pages[i].active = false;
            }
        }
        spin_unlock_irqrestore(&g_rx_lock, f2);
        pr_info("[RX] Old instance cleaned on process switch.\n");
    }

    /* 查找已有 shadow page（同进程重复注入） */
    spin_lock_irqsave(&g_rx_lock, flags);
    for (i = 0; i < MAX_RX_PAGES; i++) {
        if (g_rx_pages[i].active &&
            g_rx_pages[i].vaddr == (req->addr & PAGE_MASK)) {
            p = &g_rx_pages[i]; break;
        }
    }
    if (p) {
        /*
         * [FIX-T] 更新已有 shadow page 内容。
         * g_game_mm 记录弱引用（不增加 mm_users）。
         */
        g_game_mm = mm;
        spin_unlock_irqrestore(&g_rx_lock, flags);

        kaddr_shadow = kmap(pfn_to_page(p->shadow_pfn));
        *(uint32_t*)((char*)kaddr_shadow+(req->addr&~PAGE_MASK)) = req->data;
        flush_dcache_page(pfn_to_page(p->shadow_pfn));
        kunmap(pfn_to_page(p->shadow_pfn));
        asm volatile("ic ialluis\n dsb ish\n isb\n" ::: "memory");
        kpm_tlbi_page(p->vaddr);

        /* [FIX-T] 立刻归还，不泄漏 mm_users */
        mmput(mm);
        put_task_struct(task);
        return 0;
    }

    /* 查找空闲槽位 */
    for (i = 0; i < MAX_RX_PAGES; i++) {
        if (!g_rx_pages[i].active) { p = &g_rx_pages[i]; break; }
    }
    if (!p) {
        spin_unlock_irqrestore(&g_rx_lock, flags);
        mmput(mm); put_task_struct(task);
        return -ENOMEM;
    }

    game_ptep = get_user_pte_and_pmd(mm, req->addr & PAGE_MASK, &game_pmd);
    if (!game_ptep) {
        spin_unlock_irqrestore(&g_rx_lock, flags);
        mmput(mm); put_task_struct(task);
        return -EFAULT;
    }

    p->vaddr        = req->addr & PAGE_MASK;
    p->orig_pte_val = pte_val(*game_ptep);
    orig_page       = pte_page(*game_ptep);
    p->orig_pfn     = page_to_pfn(orig_page);

    spin_unlock_irqrestore(&g_rx_lock, flags);

    /* Shadow page 分配与初始化（可睡眠，在锁外） */
    shadow_page = alloc_page(GFP_KERNEL | __GFP_ZERO);
    if (!shadow_page) {
        mmput(mm); put_task_struct(task);
        return -ENOMEM;
    }
    p->shadow_pfn = page_to_pfn(shadow_page);

    kaddr_orig   = kmap(orig_page);
    kaddr_shadow = kmap(shadow_page);
    memcpy(kaddr_shadow, kaddr_orig, PAGE_SIZE);
    *(uint32_t*)((char*)kaddr_shadow+(req->addr&~PAGE_MASK)) = req->data;
    flush_dcache_page(shadow_page);
    kunmap(shadow_page);
    kunmap(orig_page);
    asm volatile("ic ialluis\n dsb ish\n isb\n" ::: "memory");

    /* 提交：持锁写入全局状态 */
    spin_lock_irqsave(&g_rx_lock, flags);

    if (g_game_mm != NULL && g_game_mm != mm) {
        /* 窗口期内又切换了进程，放弃本次注入 */
        spin_unlock_irqrestore(&g_rx_lock, flags);
        __free_page(shadow_page);
        mmput(mm); put_task_struct(task);
        return -EAGAIN;
    }

    /*
     * [FIX-T] 记录弱引用：
     *   此处 mm_users >= 1（我们还持有 get_task_mm 的引用），
     *   记录指针是安全的。函数末尾 mmput 后指针仍指向有效结构
     *   （因为进程本身还持有 mm_users），直到 exit_mmap 触发时
     *   我们的 hook 会清空 g_game_mm。
     */
    g_game_mm  = mm;
    p->active  = true;

    need_write_pte   = true;
    pte_val_to_write = build_orig_pte(p);

    if (!READ_ONCE(g_kernel_hooked)) {
        spin_unlock_irqrestore(&g_rx_lock, flags);

        {
            uint32_t reloc_buf[ESCAPE_POD_SLOTS];
            int reloc_cnt;
            const uint32_t *orig_ptr;

            /* Hook 1: do_fault */
            orig_ptr = (const uint32_t*)(k_do_fault & ~3UL);
            memcpy(g_hook_fault.orig_insns, orig_ptr+1,
                   HOOK_PROLOGUE_INSNS*sizeof(uint32_t));
            g_hook_fault.addr      = k_do_fault + 4;
            g_hook_fault.installed = false;

            reloc_buf[0] = 0xD503249F;
            reloc_cnt = arm64_relocate_insns(
                reloc_buf+1, (unsigned long)my_escape_pod+4,
                orig_ptr+1, k_do_fault+4, 4);
            if (reloc_cnt > 0) {
                reloc_buf[1+reloc_cnt+0] = 0x58000050;
                reloc_buf[1+reloc_cnt+1] = 0xD61F0200;
                *((uint64_t*)&reloc_buf[1+reloc_cnt+2]) = k_do_fault+20;
                safe_vmap_patch((unsigned long)my_escape_pod,
                                reloc_buf, 1+reloc_cnt+4);
            }
            hook_insns[0]=0x58000050; hook_insns[1]=0xD61F0200;
            *((uint64_t*)&hook_insns[2]) = (uint64_t)my_fault_trampoline;
            safe_vmap_patch(k_do_fault+4, hook_insns, HOOK_PROLOGUE_INSNS);
            g_hook_fault.installed = true;

            /* Hook 2: exit_mmap */
            if (k_exit_mmap) {
                orig_ptr = (const uint32_t*)(k_exit_mmap & ~3UL);
                memcpy(g_hook_exit_mmap.orig_insns, orig_ptr+1,
                       HOOK_PROLOGUE_INSNS*sizeof(uint32_t));
                g_hook_exit_mmap.addr      = k_exit_mmap + 4;
                g_hook_exit_mmap.installed = false;

                reloc_buf[0] = 0xD503249F;
                reloc_cnt = arm64_relocate_insns(
                    reloc_buf+1, (unsigned long)my_exit_mmap_escape_pod+4,
                    orig_ptr+1, k_exit_mmap+4, 4);
                if (reloc_cnt > 0) {
                    reloc_buf[1+reloc_cnt+0] = 0x58000050;
                    reloc_buf[1+reloc_cnt+1] = 0xD61F0200;
                    *((uint64_t*)&reloc_buf[1+reloc_cnt+2]) = k_exit_mmap+20;
                    safe_vmap_patch((unsigned long)my_exit_mmap_escape_pod,
                                    reloc_buf, 1+reloc_cnt+4);
                }
                hook_insns[0]=0x58000050; hook_insns[1]=0xD61F0200;
                *((uint64_t*)&hook_insns[2]) = (uint64_t)my_exit_mmap_trampoline;
                safe_vmap_patch(k_exit_mmap+4, hook_insns, HOOK_PROLOGUE_INSNS);
                g_hook_exit_mmap.installed = true;
            }
        }

        spin_lock_irqsave(&g_rx_lock, flags);
        WRITE_ONCE(g_kernel_hooked, true);
        pr_info("[RX] KPM V13 Online.\n");
    }

    spin_unlock_irqrestore(&g_rx_lock, flags);

    /* [FIX-O] 出锁后写 PTE */
    if (need_write_pte)
        pte_write_locked(mm, p->vaddr, game_pmd, game_ptep, pte_val_to_write);

    /*
     * [FIX-T] 任务完成，归还 get_task_mm 持有的引用。
     *
     * 此后 g_game_mm 是真正的弱引用：
     *   - 进程正常运行：mm_users >= 1（进程自身持有），指针有效。
     *   - 进程退出：exit_mmap hook 触发，g_game_mm 被置 NULL。
     *   - 任何读取路径：必须通过 mmget_not_zero() 升级后才能解引用。
     */
    mmput(mm);
    put_task_struct(task);
    return 0;
}

/* -----------------------------------------------------------------------
 * workqueue 执行体
 * ----------------------------------------------------------------------- */
static void rx_inject_work_fn(struct work_struct *work)
{
    struct rx_work_item *item = container_of(work, struct rx_work_item, work);
    int ret = inject_and_setup_rx(&item->req);
    if (ret) pr_warn("[RX] inject returned %d\n", ret);
    kfree(item);
}

/* -----------------------------------------------------------------------
 * Netlink 接收回调（FIX-L）
 * ----------------------------------------------------------------------- */
static void nl_recv_msg(struct sk_buff *skb)
{
    struct nlmsghdr     *nlh;
    struct rx_patch_req *req;
    struct rx_work_item *item;

    if (skb->len < nlmsg_total_size(sizeof(struct rx_patch_req))) return;
    nlh = nlmsg_hdr(skb);
    if (!nlmsg_ok(nlh, skb->len)) return;
    if (nlmsg_len(nlh) < (int)sizeof(struct rx_patch_req)) return;
    req  = (struct rx_patch_req*)nlmsg_data(nlh);
    item = kmalloc(sizeof(*item), GFP_ATOMIC);
    if (!item) { pr_err("[RX] OOM\n"); return; }
    item->req = *req;
    INIT_WORK(&item->work, rx_inject_work_fn);
    queue_work(g_rx_wq, &item->work);
}

/* -----------------------------------------------------------------------
 * 模块初始化 / 退出
 * ----------------------------------------------------------------------- */
static int __init rx_shadow_init(void)
{
    struct netlink_kernel_cfg cfg = { .input = nl_recv_msg };
    g_rx_wq = create_singlethread_workqueue("rx_engine_wq");
    if (!g_rx_wq) return -ENOMEM;
    nl_sk = netlink_kernel_create(&init_net, NETLINK_WUWA, &cfg);
    if (!nl_sk) { destroy_workqueue(g_rx_wq); return -ENOMEM; }
    pr_info("[RX] KPM V13 loaded.\n");
    return 0;
}

static void __exit rx_shadow_exit(void)
{
    if (nl_sk)   netlink_kernel_release(nl_sk);
    if (g_rx_wq) { flush_workqueue(g_rx_wq); destroy_workqueue(g_rx_wq); }

    /* 模块卸载时手动清理（游戏仍在运行的情况） */
    {
        unsigned long flags;
        int i;
        spin_lock_irqsave(&g_rx_lock, flags);
        g_game_mm = NULL;
        for (i = 0; i < MAX_RX_PAGES; i++) {
            if (g_rx_pages[i].active) {
                __free_page(pfn_to_page(g_rx_pages[i].shadow_pfn));
                g_rx_pages[i].active = false;
            }
        }
        spin_unlock_irqrestore(&g_rx_lock, flags);
    }

    do_safe_unhook(&g_hook_fault);
    do_safe_unhook(&g_hook_exit_mmap);

    pr_info("[RX] KPM V13 unloaded safely.\n");
}

module_init(rx_shadow_init);
module_exit(rx_shadow_exit);

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
MODULE_AUTHOR("Reverse Engineering Expert");
MODULE_DESCRIPTION("Android WuWa - R^X Dynamic Shadow Engine (Kernel Hook)");

#define NETLINK_WUWA 29 

/* --- 核心状态机定义 --- */
#define ESR_ELx_EC_SHIFT    26
#define EC_INSN_ABORT_L     0x20  // 指令异常 (取指失败)
#define EC_DATA_ABORT_L     0x24  // 数据异常 (读取失败)

#define PTE_USER_XN      (1ULL << 54) // UXN
#define PTE_AP_READ_ONLY (3ULL << 6)  // AP[2:1]
#define PTE_AP_NO_READ   (0ULL << 6)  // 警告：依赖 CPU 硬件特性

/* --- 通信协议 --- */
struct rx_patch_req {
    pid_t pid;
    uint64_t target_vaddr;        // 游戏里的要修改的地址
    uint32_t patch_data;          // 机器码
    uint64_t do_fault_kaddr;      // 用户态传来的 do_translation_fault 地址
    uint64_t init_mm_kaddr;       // 用户态传来的 swapper_pg_dir (init_mm) 地址
};

/* --- 全局变量 --- */
static struct sock *nl_sk = NULL;
static uint64_t g_target_vaddr = 0;
static uint64_t g_orig_pfn = 0;
static uint64_t g_shadow_pfn = 0;
static struct mm_struct *g_game_mm = NULL;
static uint8_t g_trampoline_escape_pod[32]; // 保存被吃掉的内核指令

#ifndef pte_pgprot
static inline pgprot_t my_pte_pgprot(pte_t pte) {
    return __pgprot(pte_val(pte) ^ pte_val(pfn_pte(pte_pfn(pte), __pgprot(0))));
}
#define pte_pgprot my_pte_pgprot
#endif

/* ==========================================================
 * 第一部分：底层的页表操控魔术
 * ========================================================== */

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

/* ==========================================================
 * 第二部分：R^X 状态切换器 (由汇编跳板调用)
 * ========================================================== */

// 返回 1 代表我们拦截处理了，返回 0 代表放行给原内核逻辑
int my_fault_dispatcher(unsigned long addr, unsigned int esr, struct pt_regs *regs) {
    if (!g_target_vaddr || (addr & PAGE_MASK) != (g_target_vaddr & PAGE_MASK)) {
        return 0; // 不是我们的地盘
    }

    unsigned int ec = esr >> ESR_ELx_EC_SHIFT;
    pte_t *ptep = get_pte_ptr(g_game_mm, g_target_vaddr);
    if (!ptep) return 0;

    unsigned long raw_pte;

    if (ec == EC_INSN_ABORT_L) {
        /* 【反作弊绕过阶段】 游戏想要执行代码：上影子页，给执行权限 */
        pte_t new_pte = pfn_pte(g_shadow_pfn, pte_pgprot(*ptep));
        raw_pte = pte_val(new_pte);
        raw_pte &= ~PTE_USER_XN;       // 允许执行
        // raw_pte &= ~PTE_AP_READ_ONLY; // 危险操作：硬件若不支持会死锁，谨慎取消注释
        raw_pte &= ~(1ULL << 52);      // 清除 ContPTE
        
        *((volatile u64 *)ptep) = raw_pte;
        force_flush_tlb_page(g_target_vaddr);
        return 1;

    } else if (ec == EC_DATA_ABORT_L) {
        /* 【反作弊绕过阶段】 游戏/反作弊想要读取数据：上原版页，给只读权限 */
        pte_t new_pte = pfn_pte(g_orig_pfn, pte_pgprot(*ptep));
        raw_pte = pte_val(new_pte);
        raw_pte |= PTE_USER_XN;        // 禁止执行！
        raw_pte |= PTE_AP_READ_ONLY;   // 允许读取
        raw_pte &= ~(1ULL << 52);
        
        *((volatile u64 *)ptep) = raw_pte;
        force_flush_tlb_page(g_target_vaddr);
        return 1;
    }

    return 0;
}

/* ==========================================================
 * 第三部分：神级裸汇编跳板 (Naked Trampoline)
 * ========================================================== */

extern int my_fault_dispatcher(unsigned long addr, unsigned int esr, struct pt_regs *regs);

__attribute__((naked)) void my_fault_trampoline(void) {
    asm volatile(
        /* 1. 保护现场：压栈保存所有可能被 C 语言污染的寄存器 */
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
        
        /* 2. 调用 C 语言调度器。进入异常时，x0=addr, x1=esr, x2=regs 是原生的 */
        "bl my_fault_dispatcher\n"

        /* 3. 检查调度器返回值 (x0) */
        "cmp x0, #1\n"
        "b.eq .L_handled\n"

        /* 4. 未被处理：恢复现场，执行逃逸舱，跳回内核原逻辑 */
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
        
        // 跳向逃逸舱 (里面存放着原函数被覆盖的头 16 字节，以及跳回原函数 +16 的指令)
        "ldr x16, =g_trampoline_escape_pod\n" 
        "br x16\n"

        /* 5. 成功处理：恢复现场，直接 eret 退回用户态！ */
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

/* ==========================================================
 * 第四部分：致命注射 (Hook 内核 PTE 并准备 R^X 双页)
 * ========================================================== */

static int inject_and_setup_rx(struct rx_patch_req *req) {
    struct task_struct *task;
    struct mm_struct *mm;
    struct page *orig_page, *shadow_page, *new_kpage;
    void *kaddr_orig, *kaddr_shadow, *kaddr_new_kernel;
    pte_t *game_ptep, *kernel_ptep;
    unsigned long flags;

    // 1. 获取游戏进程信息
    rcu_read_lock();
    task = pid_task(find_vpid(req->pid), PIDTYPE_PID);
    if (task) get_task_struct(task);
    rcu_read_unlock();
    if (!task) return -ESRCH;

    mm = get_task_mm(task);
    if (!mm) { put_task_struct(task); return -EINVAL; }
    g_game_mm = mm;
    g_target_vaddr = req->target_vaddr;

    // 2. 准备两套游戏物理页 (原页与影子页)
    game_ptep = get_pte_ptr(mm, g_target_vaddr);
    if (!game_ptep) goto out;

    orig_page = pte_page(*game_ptep);
    g_orig_pfn = page_to_pfn(orig_page);

    shadow_page = alloc_page(GFP_HIGHUSER | __GFP_ZERO);
    g_shadow_pfn = page_to_pfn(shadow_page);
    
    kaddr_orig = kmap(orig_page);
    kaddr_shadow = kmap(shadow_page);
    memcpy(kaddr_shadow, kaddr_orig, PAGE_SIZE);
    
    // 在影子页里打上修改码
    *(uint32_t *)((char *)kaddr_shadow + (g_target_vaddr & ~PAGE_MASK)) = req->patch_data;
    kunmap(shadow_page);
    kunmap(orig_page);

    // 初始状态：设为原版页，并设为【不可执行】(逼迫 CPU 在执行时发生异常)
    unsigned long raw_game_pte = pte_val(*game_ptep);
    raw_game_pte |= PTE_USER_XN;
    *((volatile u64 *)game_ptep) = raw_game_pte;
    force_flush_tlb_page(g_target_vaddr);

    // 3. 开始克隆内核函数所在的物理页！
    kernel_ptep = get_pte_ptr((struct mm_struct *)req->init_mm_kaddr, req->do_fault_kaddr);
    if (!kernel_ptep) goto out;

    new_kpage = alloc_page(GFP_KERNEL | __GFP_ZERO);
    kaddr_new_kernel = page_address(new_kpage);
    memcpy(kaddr_new_kernel, (void *)(req->do_fault_kaddr & PAGE_MASK), PAGE_SIZE);

    // 4. 构建逃逸舱与跳板 (KCFI 绕过核心)
    unsigned long offset = req->do_fault_kaddr & ~PAGE_MASK;
    uint32_t *patch_addr = (uint32_t *)((char *)kaddr_new_kernel + offset);
    
    // 保存原 16 字节到逃逸舱
    memcpy(g_trampoline_escape_pod, patch_addr, 16);
    
    // 在逃逸舱末尾追加一个跳回原函数 + 16 处的绝对跳转
    uint32_t *escape_tail = (uint32_t *)(g_trampoline_escape_pod + 16);
    escape_tail[0] = 0x58000050; // LDR X16, #8
    escape_tail[1] = 0xD61F0200; // BR X16
    *((uint64_t *)&escape_tail[2]) = req->do_fault_kaddr + 16;

    // 覆盖新内核页的开头 16 字节，使其跳向我们的纯汇编 Trampoline
    patch_addr[0] = 0x58000050; // LDR X16, #8
    patch_addr[1] = 0xD61F0200; // BR X16
    *((uint64_t *)&patch_addr[2]) = (uint64_t)my_fault_trampoline;

    // 5. 核爆瞬间：强写系统内核 PTE
    unsigned long raw_kpte = pte_val(pfn_pte(page_to_pfn(new_kpage), pte_pgprot(*kernel_ptep)));
    raw_kpte &= ~(1ULL << 52); // 去除内核的 Cont 标志

    local_irq_save(flags); // 关中断！锁命！
    *((volatile u64 *)kernel_ptep) = raw_kpte;
    
    // 全局暴力刷新
    asm volatile("dsb ishst\ntlbi vmalle1is\ndsb ish\nisb\nic ialluis\ndsb ish\nisb\n" ::: "memory");
    local_irq_restore(flags); // 开中断！

    pr_info("[RX_SHADOW] Ultimate Kernel Hook Injected! R^X Engine Online.\n");

out:
    mmput(mm); put_task_struct(task);
    return 0;
}

/* ==========================================================
 * 第五部分：无文件 Netlink 通信
 * ========================================================== */

static void nl_recv_msg(struct sk_buff *skb) {
    struct nlmsghdr *nlh;
    struct rx_patch_req *req;

    if (skb->len >= nlmsg_total_size(0)) {
        nlh = nlmsg_hdr(skb);
        if (nlmsg_len(nlh) >= sizeof(struct rx_patch_req)) {
            req = (struct rx_patch_req *)nlmsg_data(nlh);
            pr_info("[RX_SHADOW] Received Init Signal. Target: 0x%llx\n", req->target_vaddr);
            // 收到用户态发来的核心地址与任务，实施致命注射！
            inject_and_setup_rx(req);
        }
    }
}

static int __init rx_shadow_init(void) {
    struct netlink_kernel_cfg cfg = { .input = nl_recv_msg, };
    nl_sk = netlink_kernel_create(&init_net, NETLINK_WUWA, &cfg);
    if (!nl_sk) return -ENOMEM;
    pr_info("[RX_SHADOW] Waiting for User-Space Target Coordinates...\n");
    return 0;
}

static void __exit rx_shadow_exit(void) {
    if (nl_sk) netlink_kernel_release(nl_sk);
    // 警告：这里没有实现内核反 Hook 清理！一旦注入，直到重启前内核都处于魔改状态。
    pr_info("[RX_SHADOW] Module unloaded (Warning: Hook remains in memory).\n");
}

module_init(rx_shadow_init);
module_exit(rx_shadow_exit);

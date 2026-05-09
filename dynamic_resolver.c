/*
 * dynamic_resolver.c - Bypassing GKI KMI Restrictions via Dummy Kprobes
 * Architecture: AArch64
 * Author: 顶尖逆向架构师
 */
#include <linux/module.h>
#include <linux/kprobes.h>
#include "dynamic_resolver.h"

/* 定义函数指针类型以接收 kallsyms_lookup_name */
typedef unsigned long (*kallsyms_lookup_name_t)(const char *name);
static kallsyms_lookup_name_t p_kallsyms_lookup_name = NULL;

/* 
 * Dummy Kprobe 探针
 * 我们只需要它注册成功那一刻的 addr 成员，无需实现 handler 
 */
static struct kprobe kp_dummy = {
    .symbol_name = "kallsyms_lookup_name",
};

int ghost_resolver_init(void)
{
    int ret;

    /* 如果系统低于 5.7，符号可能仍然导出，我们直接强转 */
    /* 但在 GKI 6.6 中，必须依赖 kprobe 萃取 */
    ret = register_kprobe(&kp_dummy);
    if (ret < 0) {
        pr_err("[Ghost Resolver] Failed to register dummy kprobe for kallsyms_lookup_name. Err: %d\n", ret);
        return ret;
    }

    /* 物理地址萃取：在注册成功后，kprobe 的 addr 字段已由系统填充完毕 */
    p_kallsyms_lookup_name = (kallsyms_lookup_name_t)kp_dummy.addr;

    /* 阅后即焚，消除探针痕迹 */
    unregister_kprobe(&kp_dummy);

    if (!p_kallsyms_lookup_name) {
        pr_err("[Ghost Resolver] Fatal: Extracted address is NULL.\n");
        return -EINVAL;
    }

    pr_info("[Ghost Resolver] Engine Online. kallsyms_lookup_name found at: 0x%lx\n", 
            (unsigned long)p_kallsyms_lookup_name);

    return 0;
}

void *ghost_resolve_sym(const char *name)
{
    unsigned long addr;

    if (unlikely(!p_kallsyms_lookup_name)) {
        pr_err("[Ghost Resolver] Not initialized!\n");
        return NULL;
    }

    addr = p_kallsyms_lookup_name(name);
    if (!addr) {
        pr_warn("[Ghost Resolver] Symbol not found: %s\n", name);
        return NULL;
    }

    return (void *)addr;
}

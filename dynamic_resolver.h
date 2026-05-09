/*
 * dynamic_resolver.h - Kprobe-Based Kallsyms Resolver for Ghost Core
 * Architecture: AArch64
 */
#ifndef _GHOST_DYNAMIC_RESOLVER_H
#define _GHOST_DYNAMIC_RESOLVER_H

#include <linux/types.h>

/*
 * 初始化动态解析引擎。
 * 返回值: 0 成功; 负数 失败 (无法定位 kallsyms_lookup_name)
 */
extern int ghost_resolver_init(void);

/*
 * 获取未导出符号的绝对内存地址。
 * name: 符号字符串
 * 返回值: 函数指针地址; NULL 表示解析失败
 */
extern void *ghost_resolve_sym(const char *name);

#endif /* _GHOST_DYNAMIC_RESOLVER_H */

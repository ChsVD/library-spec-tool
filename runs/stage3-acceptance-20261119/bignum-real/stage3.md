# 阶段三公共内容

已审核 0 / 1 条需求，待处理 0 条，共享条目 0 项。
当前状态 `partial`，模型请求 2 次，参考原文读取 0 字符。

## 逐需求交付

### definition · Model the fields read by downstream code; distinguish the target probe from the whole representation.

`fn-85c3fb94fe0d59f1da3de85f:1:d8cffa7d77a034c4`

For OpenSSL struct BIGNUM (bignum_st): find reference definitions describing a dynamic signed multiple-precision number, its backing limb array and which prefix is used. Need a connection between memory fields d (least-significant limb first), top (used length), dmax (allocated capacity), neg (sign), and the mathematical integer. Identify which fields, ownership and value interpretation the precedent actually supports and any layout adaptations.

上游状态 `approved`。在交付的 Linux x86_64、C11 配置下，project/target/normalized.c:1–8 确认 d 的类型为 BN_ULONG *，BN_ULONG 是 unsigned long long 的别名。第 18–21 行支持 read_data_field 情景：若 p 指向有效对象且 d 字段已初始化并可合法读取，函数只读取该字段，返回入口指针值（含空指针），且无内存写入。其他字段无需初始化，函数不访问 d 所指存储。注释在入口和返回时使用同一字段存储断言。草案明确排除了非法字段读取和对所指存储的额外保证。交付材料未列出调用情景，也未确认 store 的形式化权限模型或 QCP 验证状态。

处理状态 `retryable`，覆盖 `uncovered`，结论 `gap`，适用性 `requires_target_validation`，目标验证 `not_run`。

**未解决事项**

- 生成任务尚未产出通过格式检查的候选。

运行受阻。model exchange exhausted its context budget

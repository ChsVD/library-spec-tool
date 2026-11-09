# 函数证明实验统计（2026-11-03）

在 library-spec-tool 的两个目标库实验中，共确认 **24 个不同的 C 函数**已在各自记录的配置和规约下完成函数体证明。OpenSSL BN 有 10 个，Simplex 有 14 个。统计按目标库和函数名去重。同一函数的不同别名契约、成功重试和重复实验均只计一个函数。以下结果取自归档验收记录，本次未重新执行证明。

## OpenSSL BN

[BN 总报告](runs/isolated-bn-words-sol61-high-20261020-01/evaluation/FINAL_EXPERIMENT_REPORT.md) 记录了首批 10 个函数、12 个证明案例。两个乘法相关函数分别验证了原地和分离输出，因此案例数比函数数多两个。

| 运算类别 | 函数 | 本轮主要范围 |
|---|---|---|
| 加减 | `bn_add_words`、`bn_sub_words` | 原地写回 `r=a`，另一输入分离；验证结果及进位／借位 |
| 单字乘法与乘加 | `bn_mul_words`、`bn_mul_add_words` | 各验证原地、分离输出两个案例；乘加需读取已初始化的旧输出 |
| 位数与除法 | `BN_num_bits_word`、`bn_div_words` | 精确位数；除法覆盖除数非零且商可由一字表示的正常域 |
| 比较 | `bn_cmp_words`、`bn_cmp_part_words` | 分离输入，验证精确大小关系，允许高位零及合法长度边界 |
| 平方与普通乘法 | `bn_sqr_words`、`bn_mul_normal` | 分离输出；前者逐字独立平方，后者计算完整多字乘积 |

验证使用选定的 64 位小端 release 配置和通用 C 实现。上表给出首批证明范围。后续加、减、乘及乘加实验再次验证了其中的函数，函数总数不变。例如 [减法重验](runs/isolated-bn-words-sol61-high-20261020-01/fresh-sub-20261027/final_summary.json) 与 [乘加复用实验](runs/isolated-bn-words-sol61-high-20261020-01/mul-add-reuse-20261029/final_summary.json) 均有最终通过记录。函数体对零长度输入满足规约，与上层以长度零调用时能否匹配该规约，需要分别核验。

## Simplex

逐项检查 checks 目录中的成功证明结果，共有 16 份通过最终检查的记录，对应以下 14 个函数。checked_add 和 checked_mul 各有初次证明和命名规约版本两份记录。表中每个链接指向该次运行的验收结果。

| 函数 | 成功运行记录 |
|---|---|
| `checked_add` | [simplex_checked_add_branches-20261102024202](runs/isolated-simplex-20261101-01/checks/checked_add_branches_proof_result.json)、[simplex_checked_add-20261101231825](runs/isolated-simplex-20261101-01/checks/checked_add_proof_result.json) |
| `checked_mul` | [simplex_checked_mul_branches-20261102002304](runs/isolated-simplex-20261101-01/checks/checked_mul_branches_proof_result.json)、[simplex_checked_mul-20261101223403](runs/isolated-simplex-20261101-01/checks/checked_mul_proof_result.json) |
| `sx_find_entering` | [simplex_find_entering-20261102041019](runs/isolated-simplex-20261101-01/checks/find_entering_proof_result.json) |
| `sx_find_violation` | [simplex_find_violation_retry-20261102093641](runs/isolated-simplex-20261101-01/checks/find_violation_retry_proof_result.json) |
| `positive_gcd` | [simplex_positive_gcd-20261101220217](runs/isolated-simplex-20261101-01/checks/positive_gcd_proof_result.json) |
| `rat_add` | [simplex_rat_add-20261102024202](runs/isolated-simplex-20261101-01/checks/rat_add_proof_result.json) |
| `rat_compare` | [simplex_rat_compare-20261102013817](runs/isolated-simplex-20261101-01/checks/rat_compare_proof_result.json) |
| `rat_div` | [simplex_rat_div-20261102015856](runs/isolated-simplex-20261101-01/checks/rat_div_proof_result.json) |
| `rat_mul` | [simplex_rat_mul-20261102004917](runs/isolated-simplex-20261101-01/checks/rat_mul_proof_result.json) |
| `rat_reduce` | [simplex_rat_reduce-20261101234250](runs/isolated-simplex-20261101-01/checks/rat_reduce_proof_result.json) |
| `rat_zero` | [simplex_rat_zero-20261102032152](runs/isolated-simplex-20261101-01/checks/rat_zero_proof_result.json) |
| `sx_initialize` | [simplex_initialize-20261103024305](runs/isolated-simplex-20261101-01/checks/sx_initialize_proof_result.json) |
| `sx_pivot` | [simplex_pivot-20261103051637](runs/isolated-simplex-20261101-01/checks/sx_pivot_proof_result.json) |
| `sx_recompute` | [simplex_recompute-20261103004647](runs/isolated-simplex-20261101-01/checks/sx_recompute_proof_result.json) |

较早的[复盘](runs/isolated-simplex-20261101-01/evaluation/SIMPLEX_PROOF_ISSUES_AND_OPTIMIZATION.md)集中讨论两个扫描函数。之后完成的 sx_recompute、sx_initialize 和 sx_pivot 均已计入上表。sx_find_violation 的早期阻断由成功重试取代。上层 sx_solve 还需要搜索调用返回后保持已知状态的契约，原有函数体证明不能直接提供这项保证。

本次查到的[批次进度](runs/isolated-simplex-20261101-01/checks/simplex_batch_progress.json)将补充的状态保持接口列在证明中，将 sx_solve、sx_check、simplex_deduction 列为后续函数。这三项未计入完成数。现有结果覆盖已列函数各自的契约，整个求解器的可行性或不可满足性结论仍需上层组合证明。

## 统计范围

仅统计本项目实验中的目标函数。参考库已有证明、候选规约、Coq 公共引理、策略以及拆分的证明目标均不计为新的函数。BN 的 12 指首批按契约区分的案例，Simplex 的 16 指成功运行记录，两者统计单位不同，因此跨库只合计去重函数数。

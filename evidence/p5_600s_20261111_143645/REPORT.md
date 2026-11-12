# 原52例最小整数单纯形测试结果

每例外部墙钟限时600秒，4路并行，普通-O2 -g构建。

结果：46例通过，6例超时，0例结果不符，0例进程异常。

52份输入SHA256与原清单一致；原清单中的可行见证及正权重矛盾证据全部通过独立精确有理数复核。返回0对应有理可行，返回1对应不可行，不作整数SAT判断。

外部时间包括解析、输入保留检查与释放；kernel_seconds只计sx_check_qcp。超时案例没有返回值或完整内核耗时，不作数学结论。600秒后终止及回收进程存在约0.1秒管理开销。并行测试不与历史不同配置耗时直接作性能优劣比较。

| 样例 | 行数 | 变量数 | 结果 | 内核秒 | 总秒 |
|---|---:|---:|---|---:|---:|
| bounded-pairs-n12-m32 | 32 | 12 | PASS | 0.000023 | 0.002 |
| bounded-pairs-n24-m64 | 64 | 24 | PASS | 0.000068 | 0.002 |
| bounded-pairs-n48-m128 | 128 | 48 | PASS | 0.000247 | 0.002 |
| common-factor-k128-n8-m16 | 16 | 8 | PASS | 0.000021 | 0.005 |
| common-factor-k32-n8-m16 | 16 | 8 | PASS | 0.000023 | 0.004 |
| common-factor-k512-n8-m16 | 16 | 8 | PASS | 0.000032 | 0.003 |
| constant-unused-n32-m320 | 320 | 32 | PASS | 0.006951 | 0.009 |
| coprime-fraction-k128-n8-m16 | 16 | 8 | PASS | 0.000078 | 0.004 |
| coprime-fraction-k32-n8-m16 | 16 | 8 | PASS | 0.000018 | 0.002 |
| coprime-fraction-k512-n8-m16 | 16 | 8 | PASS | 0.000018 | 0.003 |
| dense-feas-n12-m48 | 48 | 12 | PASS | 0.038278 | 0.041 |
| dense-feas-n16-m64 | 64 | 16 | PASS | 0.046176 | 0.048 |
| dense-feas-n24-m96 | 96 | 24 | PASS | 1.175548 | 1.178 |
| dense-feas-n4-m16 | 16 | 4 | PASS | 0.000178 | 0.002 |
| dense-feas-n6-m24 | 24 | 6 | PASS | 0.000418 | 0.003 |
| dense-feas-n8-m32 | 32 | 8 | PASS | 0.002474 | 0.004 |
| dense-unsat-n12-m48 | 48 | 12 | PASS | 0.018451 | 0.020 |
| dense-unsat-n16-m64 | 64 | 16 | PASS | 0.643086 | 0.645 |
| dense-unsat-n4-m16 | 16 | 4 | PASS | 0.000303 | 0.002 |
| dense-unsat-n6-m24 | 24 | 6 | PASS | 0.000542 | 0.006 |
| dense-unsat-n8-m32 | 32 | 8 | PASS | 0.002224 | 0.004 |
| fraction-n16-m32 | 32 | 16 | PASS | 0.000045 | 0.001 |
| fraction-n32-m64 | 64 | 32 | PASS | 0.000134 | 0.002 |
| fraction-n4-m8 | 8 | 4 | PASS | 0.000028 | 0.004 |
| fraction-n64-m128 | 128 | 64 | PASS | 0.000468 | 0.002 |
| fraction-n8-m16 | 16 | 8 | PASS | 0.000019 | 0.006 |
| independent-unsat-n32-m64 | 64 | 32 | PASS | 0.000064 | 0.001 |
| independent-unsat-n64-m128 | 128 | 64 | PASS | 0.000232 | 0.002 |
| independent-unsat-n8-m16 | 16 | 8 | PASS | 0.000009 | 0.005 |
| late-constant-unsat-n32-m160 | 160 | 32 | PASS | 19.195022 | 19.197 |
| one-sided-n100-m400 | 400 | 100 | TIMEOUT | — | 600.108 |
| one-sided-n16-m64 | 64 | 16 | PASS | 0.031855 | 0.033 |
| one-sided-n16-m64-reversed | 64 | 16 | PASS | 0.039759 | 0.041 |
| one-sided-n32-m128 | 128 | 32 | PASS | 10.178402 | 10.181 |
| one-sided-n64-m256 | 256 | 64 | TIMEOUT | — | 600.098 |
| pair-growth-n3-m24 | 24 | 3 | PASS | 0.000589 | 0.005 |
| pair-growth-n4-m32 | 32 | 4 | PASS | 0.000019 | 0.004 |
| pair-growth-n5-m40 | 40 | 5 | PASS | 0.000279 | 0.002 |
| pair-growth-n6-m48 | 48 | 6 | PASS | 0.000056 | 0.002 |
| redundant-n16-m320 | 320 | 16 | PASS | 0.003839 | 0.008 |
| redundant-n4-m80 | 80 | 4 | PASS | 0.000440 | 0.003 |
| redundant-n8-m160 | 160 | 8 | PASS | 0.001438 | 0.004 |
| sparse-feas-n100-m320 | 320 | 100 | TIMEOUT | — | 600.100 |
| sparse-feas-n16-m64 | 64 | 16 | PASS | 0.006712 | 0.009 |
| sparse-feas-n32-m128 | 128 | 32 | PASS | 5.318930 | 5.321 |
| sparse-feas-n64-m256 | 256 | 64 | TIMEOUT | — | 600.113 |
| sparse-feas-n8-m32 | 32 | 8 | PASS | 0.000761 | 0.003 |
| sparse-unsat-n100-m320 | 320 | 100 | TIMEOUT | — | 600.116 |
| sparse-unsat-n16-m64 | 64 | 16 | PASS | 0.008399 | 0.009 |
| sparse-unsat-n32-m128 | 128 | 32 | PASS | 5.908087 | 5.910 |
| sparse-unsat-n64-m256 | 256 | 64 | TIMEOUT | — | 600.116 |
| sparse-unsat-n8-m32 | 32 | 8 | PASS | 0.002112 | 0.003 |

本轮仅新增测试驱动及脚本、实验记录，未修改生产内核或原实验。测试驱动沿用合法输入构造并检查输入不变；无内核预算或UNKNOWN。

复测：在项目目录编译 tests/bench_driver.c 链接 build/libsx.a 生成 build/bench_driver，再运行 python3 tests/run_p5.py。脚本创建新的带时间目录，不覆盖本次证据。

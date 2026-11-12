# 首批优化验收 2026年11月12日

本批仅增加常数矛盾快判和换基后整行正GCD约简。无变量压缩、输入整行缩放、映射、中间矩阵、预算、UNKNOWN、见证或独立生产检查器。

原版 solver.c 和测试可执行文件保存在本目录 baseline_solver.c、baseline_driver。当前自有源码及头文件266行，增加38行；solver.c从155行增至193行。

588数学例及90次实际换基恒等式测试通过，普通和ASan/UBSan均通过，保留普通-O2 -g构建。日志见本目录test.log、sanitize.log、normal.log。

52例复测：51 PASS、1 TIMEOUT、0 MISMATCH、0 ERROR；每例外部600秒，4路并行，与上轮调度相同。上轮46 PASS、6 TIMEOUT。该对照是两批单次观测，不是重复统计；小案例可能因新增GCD成本而变慢。

| 样例 | 优化前内核秒／状态 | 优化后内核秒／状态 |
|---|---:|---:|
| bounded-pairs-n12-m32 | 2.3107e-05 | 2.3091e-05 |
| bounded-pairs-n24-m64 | 6.7813e-05 | 8.0181e-05 |
| bounded-pairs-n48-m128 | 0.000247199 | 0.000235954 |
| common-factor-k128-n8-m16 | 2.1003e-05 | 2.6426e-05 |
| common-factor-k32-n8-m16 | 2.2738e-05 | 1.8899e-05 |
| common-factor-k512-n8-m16 | 3.2287e-05 | 2.8641e-05 |
| constant-unused-n32-m320 | 0.006951417 | 0.010696253 |
| coprime-fraction-k128-n8-m16 | 7.7674e-05 | 2.7227e-05 |
| coprime-fraction-k32-n8-m16 | 1.8051e-05 | 2.0134e-05 |
| coprime-fraction-k512-n8-m16 | 1.7669e-05 | 2.5392e-05 |
| dense-feas-n12-m48 | 0.038277672 | 0.030922006 |
| dense-feas-n16-m64 | 0.046175867 | 0.033978556 |
| dense-feas-n24-m96 | 1.175548194 | 0.233867936 |
| dense-feas-n4-m16 | 0.000177581 | 0.00058905 |
| dense-feas-n6-m24 | 0.000418471 | 0.000988916 |
| dense-feas-n8-m32 | 0.002474461 | 0.005385453 |
| dense-unsat-n12-m48 | 0.01845142 | 0.019292412 |
| dense-unsat-n16-m64 | 0.643085642 | 0.141403432 |
| dense-unsat-n4-m16 | 0.000302519 | 0.000545212 |
| dense-unsat-n6-m24 | 0.000541699 | 0.001172262 |
| dense-unsat-n8-m32 | 0.002223792 | 0.004703882 |
| fraction-n16-m32 | 4.5323e-05 | 6.1887e-05 |
| fraction-n32-m64 | 0.000133976 | 0.000145449 |
| fraction-n4-m8 | 2.8424e-05 | 2.4477e-05 |
| fraction-n64-m128 | 0.000467763 | 0.000522605 |
| fraction-n8-m16 | 1.9477e-05 | 2.9561e-05 |
| independent-unsat-n32-m64 | 6.4391e-05 | 8.1238e-05 |
| independent-unsat-n64-m128 | 0.000232449 | 0.000258043 |
| independent-unsat-n8-m16 | 9.479e-06 | 1.5243e-05 |
| late-constant-unsat-n32-m160 | 19.195021693 | 1.929e-06 |
| one-sided-n100-m400 | TIMEOUT | TIMEOUT |
| one-sided-n16-m64 | 0.031855467 | 0.037844122 |
| one-sided-n16-m64-reversed | 0.039758836 | 0.04565499 |
| one-sided-n32-m128 | 10.178402362 | 0.8976024 |
| one-sided-n64-m256 | TIMEOUT | 53.085182215 |
| pair-growth-n3-m24 | 0.000588567 | 9.905e-06 |
| pair-growth-n4-m32 | 1.8778e-05 | 1.8217e-05 |
| pair-growth-n5-m40 | 0.00027937 | 5.7272e-05 |
| pair-growth-n6-m48 | 5.6321e-05 | 3.5782e-05 |
| redundant-n16-m320 | 0.003839283 | 0.003369173 |
| redundant-n4-m80 | 0.000440146 | 0.000929959 |
| redundant-n8-m160 | 0.001438305 | 0.000989729 |
| sparse-feas-n100-m320 | TIMEOUT | 287.54421761 |
| sparse-feas-n16-m64 | 0.006711533 | 0.011793452 |
| sparse-feas-n32-m128 | 5.318930173 | 0.985733828 |
| sparse-feas-n64-m256 | TIMEOUT | 78.535619462 |
| sparse-feas-n8-m32 | 0.000760986 | 0.001932018 |
| sparse-unsat-n100-m320 | TIMEOUT | 370.891957434 |
| sparse-unsat-n16-m64 | 0.008399215 | 0.01625246 |
| sparse-unsat-n32-m128 | 5.908087127 | 1.105687572 |
| sparse-unsat-n64-m256 | TIMEOUT | 55.056850108 |
| sparse-unsat-n8-m32 | 0.002112435 | 0.005321329 |

只有one-sided-n100-m400仍超时，未赋予数学结论。常数矛盾快判避免先求解其他行；行规范化保持相同基选择方向并压缩整数表示。大案例收益支持首批保留，但一般终止性和后端容量仍待证明。

新增证明义务：gcd(D,C,A)>0及整除；统一正缩放保持方程；规范化枢轴后必须使用新的D更新P。代码使用独立临时整数，复核未引入非法别名。测试中的等价检查不进入生产路径。

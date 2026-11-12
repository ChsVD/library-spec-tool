# GMP FME 与两个整数单纯形版本的历史结果对照

相同52份输入；旧整数版输入SHA与本轮逐项一致。GMP FME采用2026-11-09正式批次（三次运行，正常完成内核时间中位数）；旧整数版采用2026-11-10 P5整数表批次；新版采用本轮单次内核耗时。

GMP FME限时2秒、地址空间512MiB；旧整数版外部3600秒、内部3570秒及内存等预算；新版外部每例600秒、4路并行、无内核预算。完成数量和耗时不是同条件重跑结果。FME不返回见证，旧整数版构造并复核见证或证据，新版仅返回0/1。

| 样例 | FME内核秒或状态 | 旧整数版内核秒或状态 | 新版内核秒或状态 |
|---|---:|---:|---:|
| bounded-pairs-n12-m32 | 0.000366 | 0.000185 | 0.000023 |
| bounded-pairs-n24-m64 | 0.002043 | 0.000500 | 0.000068 |
| bounded-pairs-n48-m128 | 0.009971 | 0.002412 | 0.000247 |
| common-factor-k128-n8-m16 | 0.000014 | 0.000947 | 0.000021 |
| common-factor-k32-n8-m16 | 0.000012 | 0.000810 | 0.000023 |
| common-factor-k512-n8-m16 | 0.000015 | 0.000733 | 0.000032 |
| constant-unused-n32-m320 | {'ERROR_ALLOC': 3} | 0.103725 | 0.006951 |
| coprime-fraction-k128-n8-m16 | 0.000013 | 0.000649 | 0.000078 |
| coprime-fraction-k32-n8-m16 | 0.000012 | 0.000668 | 0.000018 |
| coprime-fraction-k512-n8-m16 | 0.000015 | 0.000851 | 0.000018 |
| dense-feas-n12-m48 | {'ERROR_ALLOC': 3} | 0.457968 | 0.038278 |
| dense-feas-n16-m64 | {'ERROR_ALLOC': 3} | 0.465253 | 0.046176 |
| dense-feas-n24-m96 | {'ERROR_ALLOC': 3} | 3.127177 | 1.175548 |
| dense-feas-n4-m16 | {'ERROR_ALLOC': 3} | 0.007204 | 0.000178 |
| dense-feas-n6-m24 | {'ERROR_ALLOC': 3} | 0.015790 | 0.000418 |
| dense-feas-n8-m32 | {'ERROR_ALLOC': 3} | 0.060012 | 0.002474 |
| dense-unsat-n12-m48 | {'ERROR_ALLOC': 3} | 0.253073 | 0.018451 |
| dense-unsat-n16-m64 | {'ERROR_ALLOC': 3} | 1.867613 | 0.643086 |
| dense-unsat-n4-m16 | {'ERROR_ALLOC': 3} | 0.008289 | 0.000303 |
| dense-unsat-n6-m24 | {'ERROR_ALLOC': 3} | 0.015872 | 0.000542 |
| dense-unsat-n8-m32 | {'ERROR_ALLOC': 3} | 0.057983 | 0.002224 |
| fraction-n16-m32 | 0.000023 | 0.002862 | 0.000045 |
| fraction-n32-m64 | 0.000049 | 0.018843 | 0.000134 |
| fraction-n4-m8 | 0.000007 | 0.000208 | 0.000028 |
| fraction-n64-m128 | 0.000207 | 0.183372 | 0.000468 |
| fraction-n8-m16 | 0.000012 | 0.000829 | 0.000019 |
| independent-unsat-n32-m64 | 0.000056 | 0.001081 | 0.000064 |
| independent-unsat-n64-m128 | 0.000197 | 0.004777 | 0.000232 |
| independent-unsat-n8-m16 | 0.000012 | 0.000138 | 0.000009 |
| late-constant-unsat-n32-m160 | {'ERROR_ALLOC': 3} | 0.000771 | 19.195022 |
| one-sided-n100-m400 | 0.000257 | SOLVER_RESOURCE | TIMEOUT |
| one-sided-n16-m64 | 0.000007 | 0.543296 | 0.031855 |
| one-sided-n16-m64-reversed | {'ERROR_ALLOC': 3} | 0.622556 | 0.039759 |
| one-sided-n32-m128 | 0.000021 | 12.831168 | 10.178402 |
| one-sided-n64-m256 | 0.000099 | 559.137007 | TIMEOUT |
| pair-growth-n3-m24 | 0.034037 | 0.000086 | 0.000589 |
| pair-growth-n4-m32 | {'ERROR_ALLOC': 3} | 0.000142 | 0.000019 |
| pair-growth-n5-m40 | {'ERROR_ALLOC': 3} | 0.000231 | 0.000279 |
| pair-growth-n6-m48 | {'ERROR_ALLOC': 3} | 0.000282 | 0.000056 |
| redundant-n16-m320 | 0.000035 | 0.170939 | 0.003839 |
| redundant-n4-m80 | 0.000004 | 0.019939 | 0.000440 |
| redundant-n8-m160 | 0.009548 | 0.033405 | 0.001438 |
| sparse-feas-n100-m320 | {'ERROR_ALLOC': 3} | SOLVER_RESOURCE | TIMEOUT |
| sparse-feas-n16-m64 | {'ERROR_ALLOC': 3} | 0.193387 | 0.006712 |
| sparse-feas-n32-m128 | {'ERROR_ALLOC': 3} | 18.699130 | 5.318930 |
| sparse-feas-n64-m256 | {'ERROR_ALLOC': 3} | 1068.611744 | TIMEOUT |
| sparse-feas-n8-m32 | {'ERROR_ALLOC': 3} | 0.027102 | 0.000761 |
| sparse-unsat-n100-m320 | {'ERROR_ALLOC': 3} | SOLVER_RESOURCE | TIMEOUT |
| sparse-unsat-n16-m64 | {'ERROR_ALLOC': 3} | 0.273975 | 0.008399 |
| sparse-unsat-n32-m128 | {'ERROR_ALLOC': 3} | 22.343608 | 5.908087 |
| sparse-unsat-n64-m256 | {'ERROR_ALLOC': 3} | 792.921169 | TIMEOUT |
| sparse-unsat-n8-m32 | {'ERROR_ALLOC': 3} | 0.062534 | 0.002112 |

旧整数版与新版共同完成46例，新版内核耗时较短43例；旧/新耗时比中位数18.80。该比值混合了功能、版本和运行环境差异，不是严格同条件加速比。
FME与新版共同完成23例，新版较快6例。微秒级差异不宜过度解释。

没有将超时写成完成耗时，也没有把旧SMT接口或早期分数单纯形误算作旧整数单纯形。

# 首批优化版本

2026-11-12。分支 simplex-gmp-minimal-opt1，父版本为 simplex-gmp-minimal-initial 的 c6fe1332233dc7c9809e1bebce5ebb7262690e1e。

本批仅增加两个生产优化：建表前正的常数矛盾行快判；换基后对枢轴行及受影响行作整行正GCD约简。二者合并构成本分支，尚不是分别启用的消融版本。

接口仍为0/1，只读输入，不提供整数SAT、见证、UNKNOWN、预算或独立运行时数学复核。自有C及头文件266行，其中solver.c为193行，比初始版增加38行。

588个数学案例、90次换基恒等式检查及ASan/UBSan通过；52例每例600秒实验51通过、1超时、无错误结论或进程异常。记录见evidence/optimization_batch1/REPORT.md和evidence/p5_600s_20261112_102404。

后续消融以固定输入、顺序、编译、资源和计时边界为基础，单独标识每项优化。此处记录后续实验基线，不提前加入其他优化、开关框架或统计接口。

INITIAL_SOURCE_HASHES.json和ACCEPTANCE.md保留初始版历史含义；当前源码指纹见evidence/optimization_batch1/source_hashes.json。文档历史绝对路径为来源信息，不是普通构建依赖。尚未完成形式化正确性、容量和终止性证明。

# 最小 GMP 整数单纯形初始版

此分支保存首批优化之前的精简内核：只返回0（有理可行）或1（不可行），不返回整数SAT、见证、UNKNOWN或资源诊断。

自有代码及头文件228行，其中solver.c为155行。无常数矛盾预扫描，无换基后整行本原化；保留GCD缩小消元乘数。输入只读，NULL终止，无尾哨兵。

## 构建和测试

在Linux/WSL运行 `make test`；`make sanitize`执行ASan/UBSan；`make normal`恢复普通-O2 -g并测试。静态库为build/libsx.a，调用者使用-Iinclude -Ivendor。只使用本目录项目MiniGMP，不链接系统GMP。

588个数学案例和90次换基检查记录见ACCEPTANCE.md。历史52例每例600秒实验为46通过、6超时，见evidence/p5_600s_20261111_143645/REPORT.md。历史批量脚本需要原案例目录，普通make test使用自编生成案例，无此依赖。

## 来源与重建边界

2026-11-12从优化前留档baseline_solver.c恢复；生产源码、头文件和两个实验脚本逐项匹配初始实验source_hashes.json。其他依赖复制自未改变的项目文件。不是从Git历史检出的原始提交。

README是本次新写的发布说明；DEVELOPMENT.md和INPUT_CONTRACT.md根据当前文档移除首批优化修订，恢复初始实现语义，不声称逐字节恢复全部初始文档。ACCEPTANCE.md和历史实验保留阶段含义。绝对路径是原实验来源信息，不是构建依赖。

合法输入、尺寸与容量可表示、分配成功和MiniGMP契约是前置条件，详见INPUT_CONTRACT.md。形式化正确性和终止性证明尚未完成。

后端许可证见vendor/QCP_LICENSE。该分支独立起始，不包含旧完整单纯形的工程历史或后续两项优化。

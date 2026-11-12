# 最小 GMP 整数单纯形 首批优化版

本分支在精简初始版基础上增加常数矛盾快判和换基后整行GCD约简，作为后续消融实验的一个基线。详细变更和父提交见 [VERSION.md](VERSION.md)。

接口 `int sx_check_qcp(const struct InequList *head, size_t variables)`：0表示有理可行，不意味着整数SAT；1表示有理不可行。只读NULL终止链表，无尾哨兵，每行n+1个项目MiniGMP整数表示c0+Σcj*xj<=0。

## 构建与测试

Linux/WSL运行 `make test`，`make sanitize`执行ASan/UBSan，`make normal`恢复-O2 -g并测试。生成build/libsx.a；调用者使用-Iinclude -Ivendor，不链接系统GMP。

[开发规约](DEVELOPMENT.md)、[输入前置条件](INPUT_CONTRACT.md)、[优化验收及52例对照](evidence/optimization_batch1/REPORT.md)。历史批量脚本需要原52例数据目录；make test使用自编生成案例，无外部案例依赖。

本版没有预算、UNKNOWN、失败恢复或生产独立数学复核。合法输入、尺寸及后端容量可表示、分配成功是前置条件。工程测试不替代形式化证明。

MiniGMP保持项目来源字节不变，许可证见vendor/QCP_LICENSE。初始版记录继续保留，不将它们表述为当前版本记录。

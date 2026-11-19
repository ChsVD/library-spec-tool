# 优化版 GMP 整数单纯形

该版本固定开启五项优化。求解器使用整数表和 MiniGMP，实现自由有理变量上的线性不等式可行性判定。

入口为 `sx_check_qcp(head, variables)`。在[输入契约](INPUT_CONTRACT.md)约定下，正常返回 `0` 当且仅当原约束系统存在有理数解，返回 `1` 当且仅当不存在有理数解。输入链表及系数资源归还给调用者。

## 构建与测试

在 Linux 或 WSL 中运行 `make` 构建 `build/all-optimized-san0/libsx.a`。使用 `make test` 运行普通测试，使用 `make sanitize` 运行 ASan/UBSan 测试。调用方使用 `-Iinclude -Ivendor`，链接随库编译的 MiniGMP。

## 规约和证明

[验证目录](verification/README.md)包含顶层和各函数的 QCP 注释源码、Rocq 定义与证明、复用的模型依赖以及原版控制器终验回执。验证采用 Arch32 BigEndian。此前的[首批优化记录](VERSION.md)和[对应验收报告](evidence/optimization_batch1/REPORT.md)记录分支的上一版。

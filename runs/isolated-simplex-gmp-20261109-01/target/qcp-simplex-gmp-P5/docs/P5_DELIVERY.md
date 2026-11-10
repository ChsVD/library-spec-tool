# P5 源码交付与复现流程

## 交付组成

源码包根目录固定为qcp-simplex-gmp-P5/，含src/include/vendor/tests/examples/tools/docs、Makefile、README和历史来源/验收/哈希记录；不含编译产物、build/format-tool、原QCP树、网络依赖。候选包名qcp-simplex-gmp-P5-candidate.tar.gz，最终包qcp-simplex-gmp-P5.tar.gz，均放原工程release/。最终审查前后由主代理逐成员比对，核心源码/测试需一致，末轮仅增加验收报告/计划/清单。

make_release.py生成包内RELEASE_MANIFEST.json及包外同名.manifest.json。schema=1，stage标明candidate/final，files为相对路径到{sha256,bytes}的映射；清单不对自身哈希，归档哈希只写包外.tar.gz.sha256。P5_HASHES也不含自身或归档文件，报告不写本包自身SHA，避免哈希循环。

## 独立干净复现

从空目录解包，运行README顺序：verify_release、make normal、make test、四个qcp_example模式、make sanitize、make normal、普通cc链接外部消费者。make normal先clean再强制普通-O2重建，避免sanitize留下的插桩.a在普通消费者中缺少ASan符号。为兼容历史reviewer脚本的SAN验证顺序，make sanitize行为保持；没有把实际插桩检查悄悄改成普通库链接。

make test仅需包内C源码/Python标准库，涵盖P1算术、P2动态表、P3默认/ALL、P4组合/资源/CLI和可编译示例。make benchmark需普通库，输出新的build/p4_benchmark_latest.json，不触碰冻结P4测量。tools/verify_release检查源码成员而不检查生成build。

纯包内两TU互操作：

```sh
make normal
cc -std=c11 -Iinclude -Ivendor tests/reviewer_p5_origin.c tests/reviewer_p5_consumer.c build/libsx_solver.a -o build/p5_consumer
./build/p5_consumer
```

需要原库的额外来源审计：check_baseline.py、原头编译模式REVIEW_ORIGINAL_QCP，以及调用它们的历史总验收脚本。没有原库时不要把该来源检查混入独立数学测试。普通库不依赖这些路径。原头缺少guard和同名运行时不能无条件混链的集成边界见PROVENANCE。

## 已知限制与审查边界

没有新算法或验证证明；数学语义、所有权、预算及限制沿P3/P4合同。发布清单证明成员完整性，不是数学正确性证明或授权声明。ASan/UBSan和自编/独立测试用于工程验收，不替代形式化验证。Linux/WSL为已测试平台；本交付不声称原生Windows/MSVC或任意ABI可直接工作。C11 unsigned int须32位，POSIX单调时钟须可用。

历史验收日志在原工作区build，源码包保留报告与复现测试而不携带整个build日志/工具。候选和最终独立审查日志/包外摘要由主代理验收报告引用；源码包内报告不自引用其归档SHA。

## 日志重建和最终证据

解包根运行`python3 tests/reviewer_p5_suite.py`可重新产生`build/reviewer_p5_suite.log`，其内部运行sanitize、P1–P4独立/开发回归、normal和普通消费者；无需原QCP路径。加`--original-headers /path/to/QCP_examples/Applications_human`才增加原头互操作审计。历史报告的build日志链接仅描述当时工作区，不是源码包运行依赖；缺失旧日志时使用随包复现脚本和最终P5报告，而不是假装旧日志已经包含。

发布校验使用显式检查/非零退出，python -O与PYTHONOPTIMIZE=1不会绕过哈希/大小校验。`python3 tools/test_release_verifier.py`会在build临时子目录验证三种模式下的原文件/篡改文件结果。vendor/QCP_LICENSE原文与LICENSE_SOURCE.json随包，不修改其来源声明。

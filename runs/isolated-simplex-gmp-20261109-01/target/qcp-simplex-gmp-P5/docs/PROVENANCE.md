# 来源、独立运行与历史审计边界

采用项目`/home/maxu/Projects/qcp-v2.2.0` commit `2e547f79fc778a99434114aed110e99045d8c6d8`中`QCP_examples/Applications_human/gmp/minigmp`，不是系统GMP，也没有混用QCP_maxu另一份实现。BASELINE_MANIFEST.json冻结61个原文件SHA256、字节数和完整原Git状态；源码在vendor/gmp/minigmp全部随包分发。

vendor只有P1既有mpz_make_odd.c显式长度扫描适配，其原文件在docs/mpz_make_odd.c.original，其余与原文件哈希一致。该适配未被称为已复现合法输入漏洞，见历史BACKEND_ADAPTATION.md；原注释/规约不代表适配代码已经形式化验证。新增runtime、分数/表/solver/preprocess、示例与测试为本项目实现；未移植Yices/Z3实现或测试。

旧int原型及Yices算法阅读来源记录保留在INT_YICES_COMPARISON.md和SOURCE_HASHES.json；它们不是运行依赖，旧结论/旧测试不作为本库验证结果。未修改原QCP、旧实验目录或权限，没有FME生产回退，没有启动QCP形式化验证。原文件声明/注释随源码保留；冻结commit根LICENSE原文完整保存在vendor/QCP_LICENSE，其来源与SHA256记录于docs/LICENSE_SOURCE.json。该notice针对取用的上游项目材料保留，不据此给新增代码重新授权；本交付没有另造或扩大任何授权声明。

## 可完全独立运行

仅需包内源码、C11编译器、ar、GNU make、Python 3标准库及Linux/WSL POSIX单调时钟，即可make all/test/examples/sanitize/normal/benchmark。普通构建不访问原QCP，不下载依赖，不依赖系统GMP、格式化器或父工作区。tools/verify_release.py只检查包内成员哈希，也无需原路径。

## 需要原始来源环境的审计

`python3 tests/check_baseline.py`校验绝对原路径、commit及冻结的完整Git状态，需要原库仍在记录位置。各历史reviewer_acceptance.py调用该脚本，因此整套“历史来源+独立数学”验收需要原来源环境；不能把缺少原路径当作数学测试失败。每个自编make test和可移植独立数学测试本身不需这些路径。

tests/reviewer_p5_origin.c可在没有上游路径时包含包内vendor整数布局，与仅含公共求解器头的consumer作为两个翻译单元编译。独立主代理也用原fme_def.h编译同一origin TU核对真实来源布局。上游MiniGMP头无include guard，不能同一TU重复包含两套整数typedef。原QCP节点coef/next布局保持；演示证明数据格式/只读所有权互操作，不承诺独立静态库能和另一套同名MiniGMP运行时无条件混合链接。集成必须避免重复mpz/分配器符号、系统GMP类型混用及跨运行时释放；本阶段不提供符号重命名适配器。

## 冻结记录

P0/P1的SOURCE_HASHES/BASELINE/ADOPTED、P2/P3/P4历史HASHES/START及验收文档保留历史含义，活动源码演进后不应期待旧活动代码哈希仍匹配。P5_START冻结交付审查起点；P5_HASHES记录最终交付活动文件，排除自身和归档输出。发布包另有RELEASE_MANIFEST.json逐成员哈希和外部归档SHA256；清单不自哈希，报告不嵌入本包哈希。重建/测试只写build，日常benchmark输出build/p4_benchmark_latest.json，不改冻结P4测量文件。

# QCP MiniGMP 独立有理数可行性检查器（P5 后续链表入口修订）

唯一顶层求解入口 `sx_check_qcp` 接受 FME 的 NULL 终止 coef/next 链表，使用精确有理数修复核心。整数系数约束为`constant+sum cj*xj<=0`。Q FEASIBLE的全整数见证对应Z SAT，分数见证对应Z UNKNOWN；Q UNSAT对应Z UNSAT。资源耗尽为Q/Z UNKNOWN，输入/OOM/内部错误单独报告。

## 源码组织

工程采用 ISO C11。公开声明、模块私有表示和函数实现分开放置，是本项目为代码审查和 QCP 验证采用的目录约定。C11 本身允许在翻译单元内定义结构体。作用域、内部链接与头文件包含的语言依据见 [WG14 N1570，§6.2.1、§6.2.2、§6.10.2](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)。

| 位置 | 内容 |
|---|---|
| `include/sx_solver_contract.h`、`include/sx_arith.h`、`include/sx_table.h` | 对调用方公开的声明和类型。链表节点只作前向声明，表以不透明类型 `SxTable` 暴露。 |
| `src/arith_types.h`、`src/table_types.h`、`src/solver_types.h` | 各模块自己的表示，包括算术事务、表布局、预处理及求解状态。仅相应实现包含这些头文件。 |
| `src/table_internal.h`、`src/runtime_scope.h`、`src/integer_ops.h`、`src/backend.h` | 跨模块使用的内部契约与后端声明。原 QCP 节点布局只在 `table_internal.h` 中维护。 |
| `src/arith.c`、`src/table.c`、`src/solver.c` | 分别实现算术、表操作与求解控制。私有函数保持 `static`，线程局部对象由所属实现定义。 |

## 从源码包到可运行例子

需要Linux/WSL、C11编译器、ar、GNU make和Python 3.9+标准库（本轮GCC 13.3/Python 3.12）。要求32位unsigned int limb；不链接系统GMP、不联网、不需要原QCP路径或格式化工具。

```sh
cd qcp-simplex-gmp-P5
make normal
make test
./build/qcp_example integer
./build/qcp_example fraction
./build/qcp_example conflict
./build/qcp_example budget
```

四个例子分别展示Q/Z的FEASIBLE/SAT、FEASIBLE/UNKNOWN及1/2见证、UNSAT/UNSAT、换基资源UNKNOWN。完整可编译调用见`examples/qcp_check.c`：使用`sx_rat_set(...,"1")`构造合法项目整数，拥有者保持到调用结束，coef仅借用整数头；原coef/next布局不变。示例在读取结果前主动释放全部输入，最后统一`sx_result_clear`，不释放借用视图。

## sanitizer与普通静态库复用

```sh
make sanitize
make normal
cc -std=c11 -Iinclude -Ivendor examples/qcp_check.c build/libsx_solver.a -o build/external_consumer
./build/external_consumer fraction
```

`make sanitize`为兼容既有独立验收脚本，仍在build生成ASan/UBSan插桩库/程序；不能随后直接用普通链接参数复用该.a。`make normal`会先清理，再强制普通`-O2`重建all及示例，所以上述完整顺序可直接复制。仅执行`make all`不保证改变已有对象的编译参数。所有普通/数学测试及示例完全使用包内源码；来源审计另述。

`build/libsx_solver.a`包含表/分数/项目整数后端；仅需要表或分数可分别用libsx_table.a、libsx_arith.a。必须使用匹配的新头和库重编译调用方，`SxSolverLimits limits={0}`完整初始化；P4扩展了结构大小，不兼容旧二进制结构。原QCP节点/调用方式保持数据格式兼容，不承诺与另一套同名MiniGMP运行时无条件混链。上游整数头无include guard，同一TU不能重复包含两套typedef；分离TU互操作例在tests/reviewer_p5_origin.c和consumer.c，详见docs/PROVENANCE.md。

## 公共接口和所有权

```c
SxSolverLimits limits = {0};
SxResult result;
sx_result_init(&result);
sx_check_qcp(head, original_variable_count, &limits, &result);
/* 按error、rational_status、integer_status分别处理，见完整示例。 */
sx_result_clear(&result);
```

`head == NULL` 表示空合取；`n == 0` 时每行仍有一个常数整数。无环链表和每行 n+1 个整数必须保持可读；NULL coef 和可读环链有独立诊断。`SxProblem` 与数组建表接口仅见 `sx_table.h`，用于内部压缩建表及 P2 独立底层测试，不属于顶层求解入口。链表判环、计数和 NULL coef 检查统一由顶层 `source_validate` 完成；内部建表接收已验证的 head、行数和变量数，不再重复扫描链表结构。原 `sx_table_create_qcp` 独立公开入口已移除，P2 调用方使用数组建表接口；内部仍检查整数表示、算术/尺寸预算、分配和表不变量。

所有输入只读，调用方保留节点/系数/limb所有权，结果拥有独立见证/局部冲突分数。result须初始化、复用前clear，clear可重复；禁止浅拷贝拥有者。对象同线程创建/使用/清理，真实节点和每行n+1项必须可读，裸指针无法检测任意悬空地址/实际数组长度。raw MiniGMP分配函数不是公共API，外部项目整数可用`sx_rat_import`深复制。

FEASIBLE发布前精确代回所有原约束；分数见证不能证明整数无解。UNSAT附已核验局部阻挡行和原边界来源，尚非完整形式化证明证书。默认100000次换基、10000ms协作时限、256MiB本次显式所有权预算；0表示默认而非无限。SPACE计入表/候选/临时/见证/证据及显式分配头，排除输入、栈、其他对象和系统分配器隐藏开销/RSS；arithmetic.max_bytes仅单事务payload。时间不是硬实时抢占。完整状态/来源契约见docs/P3_CONTRACT.md、P4_CONTRACT.md。

## 命令行与优化对照

```sh
./build/solver_cli <<'EOF'
2 1
1 -2
-1 2
EOF
```

stdin为m n再接每行constant c1..cn；CLI 构造原布局链表并调用 sx_check_qcp，stdout单JSON。上例2x=1拆两行，返回Q FEASIBLE、Z UNKNOWN及1/2。选项包括`--pivots --ms --bytes --limbs --arith-bytes --fail-at`各接无符号整数。NUL、坏格式、读取错误拒绝发布JSON。

P4默认四项预处理全开；disable_optimizations的1/2/4/8位分别禁用真常数行删除、常数矛盾快判、未用变量压缩、整行正GCD约分，SX_OPT_ALL=15全关；CLI `--disable-opts 15`。先验证整个输入，见证/冲突始终恢复原行列及尺度。collect_matrix_stats默认0，显式CLI `--matrix-stats 1`才做额外O(mN)扫描。

```sh
make benchmark
```

日常复测写`build/p4_benchmark_latest.json`，不覆盖冻结的docs/P4_BENCHMARK.json。可显式运行`python3 tests/benchmark_preprocess.py --output 新路径`保存另一份测量。当前P4开/关对照不是历史P3二进制比较；冻结样例的计时边界与测量见docs/P4_BENCHMARK.md。稠密微小时差不宣称加速，有限预算下开关也可能改变是否完成。

## 发布核验、来源与限制

本工作树已移除原顶层数组入口；这是 P5 后续源码修改，须重编译调用方。原 P5 归档、RELEASE_MANIFEST.json、P5_HASHES.json 和历史报告保留为原发布证据，不代表当前源码内容。对本工作树直接执行原 `tools/verify_release.py` 会报告预期的成员差异；该工具应用于原始 P5 归档。

原包内RELEASE_MANIFEST.json对每个源成员记录SHA256/字节数，排除自身；包外.tar.gz.sha256记录归档哈希。`tools/verify_release.py`仅检查包内文件，无原路径依赖。重新打包可用tools/make_release.py，排除build/release/pycache；最终源码/报告冻结记录在P5_HASHES.json，自身与归档输出不自哈希。

`tests/check_baseline.py`及历史总验收脚本中的来源检查需要冻结原QCP绝对路径/Git状态；它们不是make test的运行依赖。来源、独立与上游两种互操作复现见docs/PROVENANCE.md；P5交付流程/报告见docs/P5_DELIVERY.md与P5_REPORT.md，历史P0–P4报告/清单保留。

仍未实现完整整数推理/SMT、增量回溯、严格实数关系、完整证明证书或QCP形式化验证；无预算终止证明未完成。每次换基仍克隆表并做完整不变量/符号检查，成本较高。原 P5 只整理构建、示例与交付；当前修订仅收敛顶层输入接口，没有增加算法。

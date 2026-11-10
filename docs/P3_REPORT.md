# P3 开发与自测报告

2026-11-09，目录`/home/maxu/qcp-simplex-gmp-20261106`。开发由同一GPT‑6.1 Sol high子代理完成，主代理独立验收另行报告。本阶段仅P3，不启动QCP形式化验证，不实现P4优化，不修改原项目/旧实验/权限或reviewer_*文件。

## 交付范围

- `src/solver.c`：生产`sx_check`/`sx_check_qcp`、结果初始化/幂等清理、确定性最小变量编号选择、有界修复循环、精确阻挡行极值及来源、独立原输入代回和Q/Z双层结果。
- `include/sx_solver_contract.h`：激活P0生产接口，增加具体诊断、统一故障注入、统计和拥有独立分数的冲突信息。QCP仅coef/next原布局，所有输入只读、无limb所有权强转。
- `src/runtime_scope.h`/`src/arith.c`：求解父scope允许私有P2子scope，全调用空间/申请序号包含见证、证据和复核临时；单调时钟elapsed安全检查，避免大时限加法溢出；P1单次事务及P2单独API预算语义保留。
- `Makefile`：独立`build/libsx_solver.a`和`build/solver_cli`，全量严格警告与测试入口。
- `tests/test_solver.c`、`tests/solver_cli.c`、`tests/check_solver.py`：本实现者新写测试/驱动，未借用外部SMT/FME测试。
- README及`docs/P3_CONTRACT.md`：状态组合、原输入所有权、结果生命周期、预算/默认值、证据限度、时间检查及CLI协议。

## 关键行为

按固定变量编号选越界基，再按固定变量编号选第一个合法方向的非基。主元为零跳过，缺失所需界视为可动；只要求方向可动，不要求完整delta在入基界内。每次成功P2换基仍执行全部不变量/符号等价检查。完成最后一次可用换基后先重新检查是否可行或冲突，确实还需再换基时才PIVOTS UNKNOWN。

无候选时独立检查各项均有阻挡界且当前值恰在该界，精确求所需最大/最小值并与违反边界作严格比较。只有充分矛盾且证据全部构造成功才UNSAT。常数矛盾允许零项阻挡列表。

可行候选先复制原变量见证，再对原只读平面输入或原链表每一行重新导入整数并精确代回。全整数见证才Z SAT；分数见证为Z UNKNOWN，不能改报整数UNSAT。所有资源耗尽公共结果均SX_OK+Q/Z UNKNOWN；OOM/无效输入/内部错误则NOT_RUN/NOT_DECIDED，任何失败均不发布半成品见证或冲突。

## 实际测试命令与结果

- `make test > build/p3-normal.log 2>&1`：通过。P3共8564个全调用逐点分配失败（平面和QCP入口），每一点均区分OOM并回收全部本次所有权；见证/证据内存失败不能产生数学结论。
- `python3 tests/check_solver.py`（含于make test）：184个精确案例/等价变换检查，另6个嵌入NUL/坏格式字节流和目录stdin I/O错误拒绝通过。
- `make sanitize > build/p3-sanitize.log 2>&1`：P1/P2/P3全部上述测试在AddressSanitizer+UndefinedBehaviorSanitizer下通过，无报告。
- P1回归保留1010个逐点故障和1000个Python Fraction精确对照；P2回归4369个逐点故障/精确空间边界及动态表检查通过。
- sanitizer后已`make clean && make test`恢复普通构建，再由主代理接管build运行独立验收。

P3 C测试覆盖空/常数行、单变量矛盾、2x=1、(x+y=3,x-y=1)精确见证(2,1)、大于64位及10^30系数、整数/分数解释、最后一次换基后的可行与冲突、需要第二次换基才耗尽的PIVOTS、输入不变及输入销毁后见证/证据仍有效、精确极值重算、无输出失败、重复清理、尺寸溢出、非法对象和配置、总空间/算术payload/limb各类限制、发布见证阶段的额外空间、ULLONG_MAX时限、协作超时。

QCP测试与平面入口对照整数/分数见证及冲突，覆盖有效尾节点、NULL空链、NULL coef、自环和多节点环、超时、超大维度，以及同一全调用逐点注入和等峰值/少1字节预算边界。Python测试检查行重排、正整数放大、重复行、增加未使用变量、9变量18行、大系数和每个发布见证的精确代回；UNSAT局部极值也独立重算。

主代理审查中发现并推动修正：时限now+duration溢出造成错误CLOCK；CLI嵌入NUL及读取失败误当EOF风险；维数不可表示与非法参数混淆；真实QCP链表需要接入P3生产循环。相应回归已包含，不隐去这些修订。

## 限制和交接

完整独立验收结果见主代理`docs/ACCEPTANCE_P3.md`，复现入口为`python3 tests/reviewer_p3_acceptance.py`，日志`build/reviewer_p3_acceptance.log`；不把独立测试数字冒称实现者自测。原61个MiniGMP文件和P0/P1/P2历史报告/冻结清单保留；P3_START_HASHES保存起点，最终P3_HASHES已包含本轮源码、文档、独立验收源码/脚本及主代理验收报告。

最小索引变体无预算终止证明仍未完成，程序使用有限换基/时间预算可靠停止；不以测试代替形式化证明。完整P2克隆和符号检查开销较高，P3不做P4优化。冲突信息是局部行依据，未实现完整原约束线性组合证书。时间为毫秒粒度协作检查，不硬抢占大数/初始化/清理；总空间只计本次显式所有权，不代表RSS。对象同线程拥有，raw MiniGMP不能在公共入口外分配；裸输入指针必须真实有效，无法探测任意悬空地址和实际数组长度。CLI输入/输出展示层在solver预算之外。仍不支持完整整数搜索、增量回溯、布尔SMT、严格实数关系或不等关系分支。

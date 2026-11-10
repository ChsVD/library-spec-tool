# P4 优化开关、映射和统计契约

2026-11-09。本轮在P3生产接口上增加可对照的预处理与工作量记录，数学范围、默认有限换基/时间预算、结果所有权和Q/Z状态组合保持P3契约。没有P4稀疏矩阵、结构选元或小整数后端，没有关闭P2完整参考检查；不运行QCP形式化验证。

## ABI与开关

SxSolverLimits与SxResult.stats扩展了字段，C调用者必须用新头文件和新静态库一起重新编译。limits应完整初始化为`SxSolverLimits limits={0}`，再设置需要的字段；不能拿旧二进制结构大小配新库。原QCP节点仍只有coef/next，sx_check_qcp签名及输入所有权不变。

`limits.disable_optimizations`为禁用位掩码：

| 位/常量 | 设为1时禁用 |
|---|---|
| 1 / SX_OPT_CONSTANT_ROWS | 删除常数真行 |
| 2 / SX_OPT_CONSTANT_CONFLICT | 常数矛盾快判 |
| 4 / SX_OPT_UNUSED_VARIABLES | 删除从未出现的原变量 |
| 8 / SX_OPT_ROW_GCD | 用整行共同正GCD约分 |
| 15 / SX_OPT_ALL | 上述全部关闭 |

0为默认全开，0..15每种组合支持数组和QCP链表；未知位是INVALID/ARGUMENT。CLI为`--disable-opts MASK`。ALL使用当前版本的P3形状路径，不做预处理；共用P4计数和最终验证零系数跳过仍存在，因此这个A/B不是冻结P3二进制的速度比较。

`limits.collect_matrix_stats`默认0，不额外扫描每张表。设为非零时在建表/每次换基后做显式O(mN)只读矩阵统计；CLI用`--matrix-stats 1`。matrix_snapshots=0代表没有测量矩阵稀疏度，不能把table_nonzeros=0误解为实际全零。

## 既有优化与新增内容

P1已有交叉约分、分母GCD、乘零/加零快捷路径；P2已有主元为零的行跳过消元、列delta增量更新和完整重算/符号等价检查。P4保留，不把它们算作本轮新交付。

P4新增共享预处理：首遍安全导入并验证全部原始整数，记录非零变量和整行正GCD；只有整个原输入验证完成才允许常数矛盾快判。QCP先完整检测环/NULL coef，再线性扫描节点；第二遍构造压缩输入也线性经过原链表，不为每行从头重新搜索。发现正的常数行后仍验证后续原行/对象；若后续错误、预算或超时先被发现，不能先发布UNSAT。

常数行所有变量系数零，constant<=0时可删除，constant>0时可发布精确常数矛盾。未出现变量可从内部表删除，原见证补0。每行g_i为常数及全部变量系数绝对值的GCD（整行零取1），只除以正g_i，不进行取整，不加入整数强化。

若首遍确认没有删行/删列且每行g_i=1，立即释放maps/scales，直接从原输入建表，避免第二份SxRat系数矩阵与借用mpz视图，也省去第二遍导入。但首遍验证和GCD工作仍有成本。真正变换时才保留原行列映射和因子，构造压缩整数副本；P2深复制建表成功后立即清理临时系数和借用视图，避免一直重复存储。

P4另在最终原行复核中跳过已验证为零的变量系数对应的导入/乘加；所有原行仍检查，且只有完整输入先经过预处理或P2导入验证后才使用该快捷路径。它对默认和ALL路径一致。

## 原问题见证与冲突映射

内部活动原变量按原编号递增、活动行按原行号递增保留；顺序保持固定编号最小选择的相对次序。内部表达式编号用活动n+i，对外一律恢复原n+原行号。删除的原变量在完整长度见证中补0，随后仍从全部原始数组行/链表节点精确代回，包括删除的真行和零系数列。预处理副本不代替原始输入复核。

令内部归一化表达式s'_i=s_i/g_i。内部冲突行若为

` s'_b = beta + sum a_j*s'_j `，

对外乘正的g_b，得到

` s_b = g_b*beta + sum (a_j*g_b/g_j)*s_j `。

具体转换：constant/required/attainable均乘g_b；阻挡项系数乘g_b/g_j，所取界乘g_j；变量编号和每个source_row映回原编号。自由原变量使用比例1。当前公共输入只有表达式上界0，所以所有实际阻挡项都有原行来源。对外转换后再次精确重算局部极值并检查严格矛盾；任何转换/证据分配失败仍按P3契约丢弃候选。

SxConflict.row独立映回原始行槽rowmap[row]；它可能不同于bound_source_row，不能二者混用。basic_variable和每个阻挡变量都使用完整原始n作为表达式偏移。常数快判直接发布原constant、原行号和原n+i，阻挡项为空。对外记录仍为局部行依据，不升级声称完整形式化证书。

## 预算与清理

maps、列出现标志、正因子、压缩系数、借用整数头数组、转换后的冲突和全部临时都在P3父scope内；元素数和字节乘法先检查溢出，继承时间检查及统一fail_at。第一遍、映射、构造副本、常数快判与冲突换算均有安全时间检查点。部分初始化按实际初始化计数清理；转换/复核未完成时不发布结果。

优化可能减少也可能增加某些工作/临时内存，因此相同有限预算下默认和ALL可能一个完成、另一个UNKNOWN。OOM、无效输入和TIME不与数学UNSAT混淆；不保证相同分配序号或峰值。首个资源/输入错误按实际发现顺序退出，绝不凭部分验证的常数行忽略后续非法对象。

## 统计精确定义

- input_rows/variables、input_cells=m*n不含常数列；input_nonzeros为变量系数非零数。active对应删除后维数/非零数，也不含常数。完整成功扫描后才把它们用于密度；错误时部分计数只是已处理前缀。
- dropped_true_rows、removed_variables、gcd_reduced_rows分别为实际删除真行、删除变量、实际约分并构造保留行的数量；constant_conflicts记录实际快判。仅计算过GCD但未构造约分行不算gcd_reduced_rows。
- preprocess_coefficients_scanned为首遍实际导入的原系数个数，含常数；ALL为0。verification_coefficients_skipped为原行复核中实际跳过的零变量系数数。
- arithmetic.rat_*计数进入公共算术事务分派的add/sub/mul/div/compare/import调用，包含在该处被OOM/预算打断的尝试；早于分派的非法参数拒绝不计。包含P2克隆/全量检查/复制、前处理及见证/冲突，复制采用add-zero也会计入，不等价于数学表达式运算次数。
- arithmetic.big_*为包装层实际发起的项目大整数add/sub/mul/gcd/divexact调用，过长度前检查后才记；包含私有整数GCD/精确整除。没有插桩MiniGMP内部辅助/递归函数，不能把它解释为所有底层指令或GCD内每次减法总数。
- max_operand_limbs是事务导入或上述包装层看到的最大操作数limb长度，包含原输入/验证临时；不是专指表系数。
- 开启collect_matrix_stats时，matrix_snapshots、matrix_cells_scanned为实际额外扫描次数/单元访问数；table_nonzeros/table_cells是最后一个快照按全部变量列（含显式零基列）统计的密度；max_coefficient_limbs为所有已采样beta/表系数的分子/分母最大limb长度。常数快判未建表或统计未开启时不产生快照。
- 所有新增累积计数饱和到SIZE_MAX；扫描计数不是估计的算术调用数。legacy comparisons仅为求解控制层比较，arithmetic.rat_compare另含P2检查等。

计数用于解释实际工作，不替代真实计时。可复现A/B见P4_BENCHMARK.md和JSON。

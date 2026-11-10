# P2 接口、表示、预算与失败契约

日期2026-11-09。本阶段仅数据结构和单次操作，未实现P3循环/sx_check，无数学状态输出；所有错误和资源耗尽均为API诊断，不是UNSAT。没有运行QCP形式化验证。

## 输入与导入

`sx_table_create(&table,&problem,limits,stats)`要求table=NULL。SxProblem行优先，每行constant及variables个整数；变量编号0..n-1为原变量，n+i为第i行表达式。每条式为`s_i=c_i0+sum c_ij*x_j`，初始基s_i、非基原变量，原变量值0、基值常数，表达式只有上界0。

`sx_table_create_qcp(&table,list,variables,limits,stats)`接受原始`struct InequList { mpz_ptr coef; struct InequList *next; }`布局。公共头只前向声明，不要求改节点或提供虚构长度字段。先用Floyd检测环，再计数/检查维数并复制每行。每个coef必须真正含n+1个可读整数，链表和limb必须可读且生命周期覆盖调用；裸指针不能验证真实存储长度或探测任意悬空地址。NULL链表合法，表示零行。零变量合法，常数真/假行保留；不进行预处理或数学冲突结论。

新增`sx_rat_import`做只读深复制：检查size不为INT_MIN、alloc非负，非零值有非零最高limb；alloc>0时必须有合法指针且size<=alloc。alloc=0允许借用静态只读常量，包括P1的静态1；调用方保证有abs(size)个有效limb。规范零可alloc=0、ptr=NULL，也可项目dummy_limb。不依赖外部整数的分配头，不释放输入。limb长度先受上限检查，再读末limb。整数只用项目32位limb表示，不通过long转换，跨32/64位不截断。结构有效不等于能验证任意裸指针地址安全。

## 表和只读访问

opaque SxTable保存原整数的精确分数副本、m个beta、按全部N=n+m变量编号的m*N稠密系数、N个赋值、上下界、边界存在标志、基/非基列表及反向索引。所有基变量列显式为零。API访问器按稳定变量身份读取，SIZE_MAX表示无对应位置，缺失界返回NULL。

成功mutation替换`*table`；此前所有借用的table/rat指针失效。失败不替换对象，原借用指针仍有效。不要缓存借用指针跨成功调用。输入可借用当前表的只读分数作为参数，操作先读取并复制后才提交，因此该种别名有效。对象只限同线程拥有，不能跨线程移交或并发使用；不能改只读内部字段或浅拷贝所有者。

bounds允许设置/删除界，要求lower<=upper；当前非基变量仍须在界内，基可越界。move只作用于非基，要求目标值在界内；用delta沿列增量更新所有基。pivot要求指定行的基变量确实违反选中的lower/upper，主元非零，入基非基在delta方向仍有移动余地；不要求全delta不超过入基原界，新基可越界。离基变量恰设为其违反边界，边界始终跟随变量身份。主元等式及更新符号见P0_CONTRACT。recompute固定非基赋值，重新计算所有基，与增量更新作精确交叉检查。

## 不变量与成本

每次create或mutation准备提交时，及显式check时，全量检查：

- 每个变量恰属于基/非基一方，列表和反查一致；所有基列为零。
- 所有分数重新导入num/den、做规范化除法并比较表示，保证分母正、最简和零0/1。
- 每个基值等于beta+sum(nonbasic coefficient*value)，非基满足其界。
- 将当前表的每个基本表达式符号代入每条原始等式，常数及每个非基系数均须为零。原始表达式系统含独立s_i列，行秩m；当前表也有m个单位基列，因此这一符号检验支持等式系统等价，而非只验证一个当前点。

检查本身不复用换基代码；主代理独立验收另用精确高斯消元作为独立对照。实现仍未形式化验证。全量符号检查约O(m*(n+1)*(n+m))次分数处理；表占用O(m*(n+m))，克隆/检查成本超过核心行操作，P2优先可审查正确性，不声称高性能。没有启用可跳过检查的生产开关；检查失败或资源不足拒绝提交。

## 总空间预算及逐点故障

SxTableLimits.max_table_bytes默认256MiB，0表示默认。计算尺寸时先检查n+m、n+1、m*(n+1)、m*N、数组元素和字节数的size_t溢出。

总空间采用实际同时存活显式申请字节计数，包含：当前目标旧表（mutation/check）、整个候选副本、原输入系数副本、动态数组、所有长期num/den limb容量、结构分配Storage头、limb分配Block头、每次算术Tx，以及内部算术和验证临时。旧表在提交前保持完整，因此克隆期间两张表都计入。创建失败的部分对象和临时先清理，再退出scope；提交先退出scope再销毁旧表。calloc/malloc前检查额度；实际成功调用的peak值在同一输入/操作/配置下可用作精确上限，少1字节会拒绝。若实际malloc失败，失败报告peak可能包含本次已预检但未成功分配的请求，此时不能作为实际RSS测量。

排除：调用方输入、其他无关表/分数、栈和私有scope本身、静态常量、malloc实现隐藏元数据/碎片以及运行库和进程其他内存。因此它是本操作所涉显式所有权空间界，不是整个进程RSS界。每张表retained_table_bytes/sx_table_bytes含自身数组和长期limb的上述头部。sx_runtime_live_bytes可检查当前线程所有本模块显式所有权字节，包含P1输出和P2结构；临时Tx退出后应回落。P1 sx_live_blocks保持仅跟踪后端分配块的原含义。

P1 arithmetic.max_bytes继续限制单个算术事务payload；max_limbs继续限制后端缓冲区及保守数值增长，两者也可独立提前拒绝。P2顶层fail_at统一枚举所有结构分配、算术Tx和底层分配的尝试；arithmetic.fail_at必须为0，非零直接ARGUMENT错误，避免两套注入编号混用。即使空表也检查算术limits合法范围。

## 错误和所有权

所有mutation先克隆，再运算/验证，最后一次提交。任何位置失败，原表、边界、赋值和借用指针保持；create失败输出仍NULL。完整清理覆盖部分初始化。后端OOM仍直接跳至算术入口捕获，不向原MiniGMP返回NULL继续运行；P2在算术返回错误后停止，释放候选。没有跨外部代码longjmp、没有外部回调；TLS不允许重入。销毁不分配，销毁NULL合法；同一非NULL地址只能销毁一次。

SxTableStats每次初始化。SX_INVALID区分ARGUMENT、OBJECT、CYCLE、BOUND、PIVOT；SX_LIMIT区分TOTAL_BYTES、ARITH_BYTES、LIMBS、OVERFLOW；SX_OOM为ALLOC；SX_INTERNAL用于INVARIANT/REENTRY。arithmetic_reason保留底层诊断。配置预算不等于真实分配失败，不生成数学UNKNOWN或UNSAT；未来P3再按具体诊断映射状态。申请次数包含触发失败的位置，peak与retained分开报告。P2无时间/换基次数控制循环，未来P3必须使用有限预算，其无预算终止证明仍未完成。

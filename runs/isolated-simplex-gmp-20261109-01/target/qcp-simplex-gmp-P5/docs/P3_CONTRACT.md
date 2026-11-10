# P3 公共求解契约、证据与资源

2026-11-09。本阶段实现完整有理数放宽检查，保留整数层的保守解释；未进行QCP形式化验证，未完成无预算终止证明。本实现没有整数搜索、割平面、FME回退、外部SMT代码/测试移植或P4性能优化。

## 公共调用及输入

公共声明在include/sx_solver_contract.h，链接build/libsx_solver.a（已包含表、分数及项目MiniGMP后端），不链接系统GMP。

```c
SxResult result;
sx_result_init(&result);
sx_check(&problem, &limits, &result);
/* 或 sx_check_qcp(head, variables, &limits, &result); */
/* 检查error、rational_status和integer_status，读取见证/冲突。 */
sx_result_clear(&result);
```

result必须先初始化且调用前为空；复用前clear。init不释放旧资源，不可用init替代clear。clear可重复、清理后恢复初始化状态；拥有的witness及blockers不可浅拷贝或单独释放，只由result_clear释放。所有模块对象限同线程创建/使用/清理，不支持信号重入或跨线程转移。传NULL out不执行工作，没有可写诊断目标。求解期间没有外部回调。

平面SxProblem为m行、n个原变量，每行n+1个只读项目整数，constant在前，表示`c0+sum cj*xj<=0`。调用方保持所有对象和limb在调用期间真实可读且不变。NULL coefficients仅在m=0时合法。尺寸不可表示在解引用前识别，返回资源UNKNOWN/SIZE_OVERFLOW；NULL必需指针、错误对象/配置为运行错误，不是数学结论。按首个被发现的错误/预算停止；非常小的预算可先于更远处非法对象的发现而耗尽。

QCP入口接受真实原布局`struct InequList { mpz_ptr coef; struct InequList *next; }`，不加长度字段、不强转其他类型。NULL链表是空问题。父资源scope内先做带时间检查的Floyd环检查、行计数及NULL coef检查，再复用P2 create_qcp；见证复核直接逐节点读取原链表。每个coef必须含n+1个可读项目整数，链表节点地址必须真实有效；裸指针不能验证实际数组长度或任意悬空内存。所有输入只读、不改next、不释放节点、不转移limb所有权。两个入口共享同一Source描述和求解循环，没有两份算法。

## 返回组合（只能按完整枚举判断）

| error | Q状态 | Z状态 | reason与发布内容 |
|---|---|---|---|
| SX_OK | FEASIBLE | SAT | NONE；全部原变量见证是整数且原始每条约束精确代回通过 |
| SX_OK | FEASIBLE | UNKNOWN | FRACTIONAL；发布精确有理数见证，不能据此否定整数解 |
| SX_OK | UNSAT | UNSAT | CONFLICT；发布已核验阻挡行证据，无见证 |
| SX_OK | UNKNOWN | UNKNOWN | SPACE/ARITH_SPACE/LIMBS/SIZE_OVERFLOW/PIVOTS/TIME；无见证、无冲突 |
| SX_INVALID | NOT_RUN | NOT_DECIDED | INVALID_INPUT，diagnostic区分ARGUMENT/OBJECT/CYCLE等；无发布内容 |
| SX_OOM | NOT_RUN | NOT_DECIDED | ALLOCATION/ALLOC；无发布内容 |
| SX_INTERNAL | NOT_RUN | NOT_DECIDED | INTERNAL，diagnostic为INVARIANT/REENTRY/CLOCK等；无发布内容 |

SX_LIMIT只用于内部算术/表资源传播，不作为公共result.error发布。diagnostic进一步区分TOTAL_BYTES和ARITH_BYTES、LIMBS、OVERFLOW、PIVOTS、TIME；arithmetic_reason保留底层原因。SX_D_DIMENSION为预留枚举，本轮不可表示尺寸实际使用OVERFLOW。

每个结果从空的内部候选构造，见证/证据部分初始化有统一清理。任何后续OOM、预算、复核失败或发布前超时都会销毁候选，不能保留未经核验的FEASIBLE/UNSAT。内部表返回前全部销毁，结果独立拥有精确分数。UNKNOWN无续算状态，可从原输入重跑。

## 确定性修复流程

初始化沿P2：原变量自由且赋值0，表达式变量s_i初始为基，值为常数，且s_i<=0。等式始终满足，非基满足边界，基允许越界。

按固定变量编号从小到大选首个越界基变量，而非按其所在行编号。若违反下界则需要增大，违反上界则需要减小。入基非基也按固定变量编号从小到大选择：

- 需增大基本值：正系数向上移动，负系数向下移动。
- 需减小基本值：正系数向下移动，负系数向上移动。
- 所需方向无界即允许；有界时当前值必须严格未达该界。零系数跳过。

只要求该方向能移动，不要求一次delta留在其原界内。P2换基把离基变量精确放在所违反的边界，新的基可以越界。每次换基后P2全量检查结构、分数、等式、非基界及符号代回原系统等价性。P3不关闭这些检查。

达到换基上限后先检查是否已经可行或能充分判冲突；只有还需要下一次换基时才PIVOTS UNKNOWN。因此完成最后一次允许换基得到的可行/矛盾不丢失。最小索引规则仍没有本项目无预算终止证明，不机械套用标准Bland定理；有限换基和协作时间预算用于可靠退出。

## 冲突依据

越界行`xb=beta+sum a_j*xj`无合法入基方向时，独立重新遍历所有非零非基项并取所需极值：违反下界时取行最大值（正系数上界、负系数下界）；违反上界时取行最小值（正系数下界、负系数上界）。每个所需界必须存在且当前非基恰在该阻挡界，随后精确计算`attainable=beta+sum coefficient*bound`。

只有最大值严格小于所需下界，或最小值严格大于所需上界，才发布UNSAT。检查失败是INTERNAL，分配失败/限制仍不得发布UNSAT。零非零项的常数矛盾同样适用。

SxConflict包含行编号、基本变量、边界来源原行编号、constant、required、attainable、to_lower以及每个阻挡项的变量、系数、所取界、上下界方向和来源原行。编号从0开始，表达式变量n+i的界来源为原行i；无原行来源用SIZE_MAX。当前平面/QCP入口只引入表达式上界0，所以实际求解轨迹的界来源均是原行；通用四方向逻辑也保留。

这是经过原等式等价检查后的局部表行极值矛盾及边界来源，不是完整追踪原行线性组合的独立证明证书，不声称完成SMT证明生成或QCP证明。测试能对局部行和原表达式做精确恒等式核对，但不能替代未来正式证书方案。

## 见证验证和整数解释

没有越界基变量后，先独立复制n个原变量分数，再逐行从原只读输入（QCP则原节点）重新导入整数系数，精确计算constant+sum coefficient*witness并要求<=0。不以当前表检查替代原约束代回。verified_rows统计成功代回的原行数。

全部原变量分母为1才发布Z SAT，否则发布Z UNKNOWN/FRACTIONAL。Q UNSAT则整数也UNSAT；分数见证不能证明整数UNSAT。空问题发布0赋值；0变量行保留常数语义，不凭行数推断可行性。

## 全程空间、时间和失败预算

SxSolverLimits中0选有限默认：max_table_bytes=256MiB，max_pivots=100000，max_milliseconds=10000；arithmetic.max_limbs和max_bytes沿P1默认（1048576 limb/64MiB单事务payload）。不存在0表示无限的歧义。允许ULLONG_MAX毫秒等很大的显式有限上限，采用elapsed比较避免now+duration溢出；单调时钟毫秒转换饱和保护边界。

求解父scope允许内部P2子scope，但不允许外部重入。父scope从建表到见证/证据发布覆盖所有本次显式申请：结构/数组、旧表与克隆候选、长期和临时limb、分配头、算术Tx、见证数组/分数、阻挡项/证据分数和复核临时。max_table_bytes现在是全调用同时存活显式所有权峰值，P2子scope仍独立执行自身限制；不会因换scope漏计长期结果。排除调用方输入、调用方SxResult本体、栈/静态对象、其他独立对象以及malloc隐藏元数据/RSS。原P1 max_bytes仍只计单次算术payload，与总限额独立。

顶层fail_at统一编号全调用每一次动态申请（含P2和Tx/见证/证据）。arithmetic.fail_at必须为0，否则INVALID/ARGUMENT。实际OOM单独报告，不混成UNKNOWN。成功调用的peak_bytes可作为同调用精确总界，少1字节会触发SPACE；失败malloc时峰值可含已经预检但未实际取得的请求，不能把它当作RSS。

CLOCK_MONOTONIC的时间检查覆盖父scope设置后、链表检查、每轮/每个变量扫描、每个显式动态申请、冲突和见证逐项/逐行、发布前。毫秒粒度可能保守提前不足1ms耗尽。大型单次整数原语、数组初始化/清理及P2既有无分配扫描不被抢占；到下个安全检查点才停止，不保证max_milliseconds墙钟硬实时。时钟读取失败或异常倒退报告INTERNAL/CLOCK；正常超时为UNKNOWN/TIME，绝不能据超时判不可行。

## 测试CLI

build/solver_cli从stdin读取`m n`，后接m*(n+1)个有符号十进制整数，按行constant在前，空白分隔。argv选项成对：`--pivots N --ms N --bytes N --limbs N --arith-bytes N --fail-at N`，0含义同API。它调用平面生产入口；QCP生产入口由C测试直接覆盖。

stdout是一个JSON对象，error/q/z/reason/diagnostic为枚举名称字符串；witness为"num/den"数组；conflict含局部极值和来源；stats含pivots/allocations/peak_bytes/comparisons/verified_rows/conflict_terms。arithmetic_reason为底层枚举数值。所有已完成的API结果（包括OOM/INVALID）exit0；输入格式、嵌入NUL、额外token、读取错误或CLI自身输入存储失败exit2且不发布JSON。读取器区分真正EOF与OOM/I/O失败；不能把失败的尾部读取当作正常EOF。

CLI创建输入整数和输出JSON文本属于调用方演示层，内存/时间在solver范围外；直接C入口才是本契约的预算对象。原始数组长度超过CLI可表示/分配规模时拒绝输入，不伪造数学状态。

# 旧 int 单纯形与 Yices 2 对照记录

日期：2026-11-06。范围为只读源码对照，没有运行测试，没有开展形式化验证。

## 结论

旧原型确实参考了 Yices 2 的单纯形算法，采用同一类“等式表＋边界＋赋值＋越界修复”流程。但已有证据支持的准确说法是“参考 Yices 2 算法后独立编写的简化原型”，不能认定为直接修改 Yices 源码而来。

旧 README 明确记录参考提交 `560f3b375840560a3decaa27c1d2f2e6503c0ab2`，列出四个阅读入口，并声明“本目录为独立简化实现，没有复制 Yices 源码”。simplex.c 文件开头也有同类声明。这些是来源自述；本次结构对照与其相符，但不是对历史开发过程的独立证明。

本地 `/home/maxu/Projects/yices2` 的 HEAD 正好为上述提交，`src/solvers/simplex/` 路径的 git status 无输出。没有使用浮动 master 代替该历史版本作本轮对照。只检查旧原型 README.txt、simplex.h、simplex.c，未读取或复用旧测试集。

## 逐项对照

| 旧原型 | Yices 2 对应入口 | 结论和差异 |
| --- | --- | --- |
| sx_initialize、sx_recompute | simplex_init_assignment，simplex.c:3575 | 都建立满足等式的赋值；旧版原变量固定从0开始，Yices 根据边界初始化非基变量 |
| sx_find_violation | simplex_check_feasibility，simplex.c:4215 | 都选越界基变量；旧版全表扫描选最小变量编号，Yices 使用不可行变量堆等状态 |
| sx_find_entering | find_entering_var_for_increase，simplex.c:3968，及 decrease 对应函数 | 都按系数与可移动边界判断修复方向；旧版按编号扫描，Yices 有结构评分及 Bland 模式 |
| sx_pivot | matrix_pivot，matrices.c:1840 | 都围绕主元重写行、消去其他行中的入基变量并交换基身份；旧版稠密表，Yices 稀疏行列索引 |
| 设置离基变量到边界，再 sx_recompute | update_to_lower_bound / upper_bound；update_non_basic_var_value，simplex.c:3640 | 数学目的相同；旧版重算全部基变量，Yices 用变化量沿关联列更新 |
| sx_solve | simplex_check_feasibility | 都在无越界时成功、无修复方向时冲突；旧版只有粗粒度数值返回码和换基预算 |

两种表方程的符号约定不能直接混用。旧版显式存储 `basic = rhs + Σ a*x`，基变量列为零；Yices matrix_pivot 把入基系数缩放到1并在其他行消去。相同数学操作不意味着系数符号和公式可以逐行照搬。

## 旧实现中直接核实的性质与限制

- SxRat 使用 int 分子、正分母；拒绝 INT_MIN，通过检查避免有符号溢出。
- SX_INPUT_VARS=8，SX_ROWS=16，状态为固定稠密数组。
- 每行增加上界为0的表达式变量，初始为基变量；原变量自由。
- 选择最小编号越界基变量，再选择编号扫描中第一个合法非基变量。
- sx_pivot 后将离基变量设为对应边界，再全量重算基变量。
- 无可进入变量返回 UNSAT；算术失败、容量和换基预算等统一返回 UNKNOWN，缺少具体诊断。
- 求解核心返回 FEASIBLE 前没有独立代回原始约束的检查；README 所述代回由测试承担。新模块必须把最终复核纳入正式路径。
- 输入链表只读、NULL 终止；旧容量检查也会最终拦截环。取消固定容量后应独立检测环。
- 算术过程中可能部分修改状态后失败，UNKNOWN 后不得续算。
- int 分数可以直接结构体赋值；迁移到拥有动态内存的大整数分数后不能机械照搬，否则可能产生浅拷贝和重复释放。
- README 明确表示未证明无上限运行一定终止，本轮不把最小编号选择声称为已证明防循环。

README 的旧测试数字只是历史记录，本轮未重跑，也不替代新 GMP 测试。

## 对开发计划的调整

旧原型现在是允许阅读和参考的项目材料。保留其易理解的数学分层和边界修复思路，但重新落实动态存储、精确大整数分数、所有权、别名、失败传播、结果枚举和最终见证复核。任何实际复用代码都应明确记录来源及改动，不能声称从未参考旧原型。

不因来源相同而继承正确性结论，不直接移植其他 SMT 的代码，不使用其测试集。原型源码不修改。

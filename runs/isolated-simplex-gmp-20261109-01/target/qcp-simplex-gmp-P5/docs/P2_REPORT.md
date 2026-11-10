# P2 实现与自测报告

2026-11-09，目录 `/home/maxu/qcp-simplex-gmp-20261106`。只实现P2；原项目源码/权限、P0/P1历史报告和清单保持不变。未实现P3循环/sx_check，未进行QCP形式化验证，没有FME回退或外部SMT测试移植。

## 交付

- `include/sx_table.h`：opaque表、平面整数输入/QCP链表创建、边界设置、非基值移动、单次边界修复换基、重算、完整检查和只读访问。
- `src/table.c`：动态稠密表、基/非基双向索引、原等式副本、边界和赋值、克隆后提交、部分初始化清理。
- `src/runtime_scope.h`及`src/arith.c`扩展：总表空间scope，计入结构/数组和长期/临时后端内存头及Tx；底层逐点故障与P2结构故障统一编号，P1原独立预算语义保持。
- `include/sx_arith.h`新增`sx_rat_import`只读安全深复制实际项目整数，支持静态alloc=0常量和真实32位limb多精度值；新增`sx_runtime_live_bytes`辅助所有权审计。
- `Makefile`新增独立静态库`build/libsx_table.a`及测试入口；原`libsx_arith.a`仍可用。新代码以-Wall -Wextra -Werror -Wpedantic -Wconversion -Wshadow编译。
- `tests/test_table.c`为本实现者自编测试；`tests/reviewer_*`仅由主代理独立验收维护，本次未编辑。
- `docs/P2_CONTRACT.md`与README详细记录输入、所有权、指针有效期、诊断、预算定义和完整检查成本。

## 实际自测

1. `make test > build/p2-normal.log 2>&1`：通过。P1保持1010个逐点故障及1000个Python Fraction CLI精确对照；P2通过4369个逐点故障，结束时无存活模块所有权字节。
2. `make sanitize > build/p2-sanitize.log 2>&1`：相同全部测试以AddressSanitizer和UndefinedBehaviorSanitizer通过，无报告。
3. sanitizer后已恢复`make clean && make test`普通构建（完成后由主代理接管build独立验收）。
4. 冻结基线61个原MiniGMP文件SHA256与完整Git本地状态再次只读核对一致；P0/P1历史报告及清单哈希与P2开始时一致。

自测覆盖：手算`s=1-x-y`和第二行`z=2+3x-y`，负主元后`x=1-s-y,z=5-3s-4y`；再次换基、精确分数及增量/重算一致；正负主元分别修复上下违反；入基变量完整delta越自身边界但方向合法；无边界；平面/实际QCP布局、输入逐字段和limb不变、链表环与NULL、空及零变量；9变量18行动态维数；2^32、-2^64-1以上整数导入及静态常量；非法对象/维数溢出/不合法limits；create/bounds/move/pivot/recompute/check逐点分配失败及回滚；create和全部mutation的成功实际峰值、等峰上限和少1字节拒绝；P1事务预算和limb预算诊断分离；新import自别名及逐点失败旧输出保持。

## 验收与限制

主代理独立验收文件和最终结果由主代理报告，不把其测试数字冒称本实现者自测。P2开始状态见P2_START_HASHES.json；交付活动代码/文档哈希见P2_HASHES.json。原ADOPTED_HASHES仍表示历史P0/P1快照，不因P2改写。

每次成功create/mutation都会完整检查分数规范化、索引分区、非基边界、赋值等式以及将当前表符号代回原始等式。后者约O(m*(n+1)*(n+m))次分数处理，克隆需同时保留旧表/候选，明显增加运行成本及峰值。本轮未作稀疏或跳检优化。

max_table_bytes是本次操作所涉显式所有权空间界：含旧表、候选表、数组、长期limb、临时、分配头及Tx，排除输入、其他对象、栈、静态数据和malloc隐藏元数据/RSS。P1 max_bytes仍仅单事务payload；不是整个进程内存界。只支持同线程所有权、合法真实可读输入存储；裸C指针无法验证任意悬空地址或数组真实长度。raw MiniGMP函数不属于公共接口。

P2只提供局部合法单步换基，不处理求解策略、循环、冲突证书、SAT/UNSAT或资源UNKNOWN映射。最小索引策略无预算终止证明仍未完成，P3仍须有限资源预算。普通测试与sanitizer不能替代形式化证明或穷尽全部输入。

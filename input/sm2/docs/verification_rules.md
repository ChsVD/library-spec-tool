# SM2 验证规则

## 1. C 源码

- 不得为了方便验证而修改 C 实现。
- QCP 无法处理源码时，先用最小实验确认前端行为和生成的 VC。
- 修改 C 实现前必须报告原因、实验结果和最小改法，并获得用户批准。
- 前端兼容改写不得改变算术顺序、分支条件、内存结果或返回值。
- 不修改当前构建不会执行的条件编译分支。

## 2. 函数规格

- 公开规格直接描述数学结果，不为简单算术表达式增加包装定义。
- 可调用函数的 `Require` 不直接使用 assertion-level `||`。该语法生成多个
  symbolic branch，而函数调用只消费一个 precondition assertion；有条件的接口
  前置应封装为含义明确的纯谓词。`Ensure` 和函数体 annotation 仍可按语义使用
  branching `||`。
- 不定义 `*_spec`、`*_contract` 等仅用于包装某个函数规格的谓词。函数 contract
  直接组合含义直观、可复用的内存谓词和数学关系。
- P 域普通值使用 `store_fp`，N 标量使用 `store_fn`。
- Montgomery 表示使用 `mont_p` 或 `mont_n`。
- Montgomery 实现的 base spec 描述直接的整数关系；表示层语义使用
  `derived_tag <= base_tag` 从对应 base spec 派生。
- 直接写入 `u32` limb 的算术接口使用字段资源
  `UInt64Array::undef_full(&(result->v[0]), 4)` 描述输出。结构体构造边界与 QCP
  生成的入口状态一致时，可以使用对应的 `UndefStructPred*`，例如
  `u1_to_u32` 的 `UndefStructPredu32` 和公钥输出的 `UndefStructPredAFPoint`。
- 不重复书写 `store_fp` 或 `store_fn` 已包含的范围条件。
- 不增加无作用的 ghost 地址等式，例如 `result == result0`。
- 分离合取已经排除重叠时，不再增加冗余的指针不等式。

## 3. 被调用函数

- 调用已验证函数时，使用该函数已有的 contract 和引理。
- callee 的签名、Require、Ensure 和 spec tag 必须与正式定义一致。
- 多规格调用使用 `where (<tag>)` 选择实际 alias 情况。
- callee contract 或 strategy 改动后，重新生成所有受影响 caller 的 VC。

## 4. Annotation 与 strategy

- 不在 C annotation 中逐层手工展开可由 strategy 处理的谓词。
- `store_u256`、`store_u256_limbs` 和四个 cell 之间的重复转换由 strategy
  处理。
- `store_u64_limbs` 展开到 `UInt64Array.full` 后，由数组 strategy 处理下标。
- SM2 全局常量由 constants strategy 展开和折叠。
- 需要导出指定纯事实时使用独立 `do` scope。
- 每个 C 文件只加载当前 case 使用的 strategy。
- C annotation 和普通 strategy 地址写成 `base + i * sizeof(type)`。只有 exec-info
  已确认 QCP 为嵌套 typed 数组或零偏移 typed alias 生成了
  `pointer_offset` 形式时，case-local strategy 才精确匹配该前端项；这类规则保持
  局部，并完成独立 soundness proof。
- `$ <name>` 选择当前 branch name，不选择 spec name。函数入口的 branch name
  通常由 spec tag 初始化。
- full assertion 必须保留后续执行需要的参数等式、局部变量和全部存活内存。
- 在 return 前增加 full assertion 时，检查 assertion 前后的地址变量仍由等式或
  同一内存谓词关联。
- 新增或修改 strategy 后，完成 soundness proof 和 goal check。
- `StructPred*`、`UndefStructPred*`、record 和结构体数组实例采用 QCP 前端生成的
  定义。公共语义谓词在其上组合数学含义，不复制一套结构体布局定义。

## 5. Rocq 库

- 不把具体函数的 Require 或 Ensure 封装进通用数学库。
- 不重复定义 `mont`、limb radix 或 SM2 常量。
- `limb_arithmetic.v` 保存通用 limb 算术。
- `montgomery.v` 保存通用 Montgomery 数学。
- `sm2_common_lib.v` 保存 SM2 表示、内存谓词、常量和 Montgomery 实例。
- `byte_encoding.v` 和 `byte_memory.v` 分别保存字节数学编码与 typed
  integer/byte-array 内存视图。
- `bitwise.v` 保存 QCP 原生位运算项的数学引理；组合概念使用明确的数学定义。
- `sm3.v` 保存标准 SM3 数学语义，`sm3_c_bridge.v` 保存 C 实现与标准语义的
  连接，`sm3_def.v` 保存生成的 `SM3_CTX` 表示及语义状态谓词。
- `sm2_protocol.v` 保存密钥、ZA、签名生成关系、标准验签关系和协议资源组。
- `almost_inverse.v` 保存参数化的 binary almost-inverse 数学。
- `basicOp_lib.v` 和 `fieldOp_lib.v` 保存对应模块的专用定义和引理。
- 只在接口更清楚并减少实际重复时增加抽象。

## 6. Rocq 证明

- manual proof、strategy proof 和正式库中不留下 `Admitted`，不新增未经明确批准的
  `Axiom`。当前批准的布局公理是 `u32_v_field_address_eq`、
  `sizeof_AFPoint_layout`、`afpoint_x_field_address_eq` 和
  `sm3_block_count_address_eq`；它们分别连接 `u32` 首字段地址、`AFPoint` typedef
  大小、`AFPoint.x` 首字段地址，以及 `SM3_CTX` 的 `nblocks` 与 `block` 字段地址
  和 QCP 的抽象 C 布局。
- 优先复用已有证明和引理。
- 先拆分分支、合取和存在量，再调用算术自动化。
- 先确定存在 witness 和关键等式，再处理分离逻辑目标。
- 清理无关上下文后再使用 `lia`、`nia`、`ring` 或 `entailer!`。
- 不在大上下文中直接调用宽范围 `nia` 或 `entailer!`。
- whole-goal manual proof 使用 `LLM_pre_process ltac:(<explicit closer>)`；需要拆分时，
  split lemma 使用同样入口，top-level 只用 `aggressive_pre_process` 和
  `Goal_apply` 组合已证 split。
- manual proof 不使用旧 `pre_process`、`pre_process_default` 或底层分离逻辑交换/
  结合 lemma；`sepcon_assoc_change` 是允许的高层重排 tactic。strategy proof 可以
  按生成的单条 strategy obligation 使用 `pre_process_default`，并保持证明直接、
  局部；不机械套用 manual 的 route 骨架。
- 只有标准 route 实测会造成明显搜索回退时才保留定向 proof，并记录具体
  VC、慢 tactic 和计时结果；不得为此修改 QCP 公共证明基础设施。
- 性能异常时使用 `coqc -time` 定位具体 tactic；单句超过 5 秒必须诊断，
  超过 15 秒的候选 proof 原则上不接受。
- `sm3_compress_entail_wit_7` 的五个顶层纯 split 使用重新泛化上下文后
  `change` 到 split goal 并 `exact` 对应证明。该 VC 的 `Goal_apply` 单次耗时
  `18.66` 至 `18.89` 秒，定向组合单次耗时 `0.009` 至 `0.023` 秒。

## 7. 生成文件

- 不手工修改 `*_goal.v`、`*_proof_auto.v`、`*_goal_check.v`。
- `*_proof_auto.v` 无需填写。
- 只在 `*_proof_manual.v` 中填写需要人工证明的 proof body。
- 重新生成时保留已有 manual proof，再迁移证明到新的 VC。
- annotation、contract 或 strategy 改动后，重新运行 symbolic execution。
- strategy 改动后，先重新生成并检查 strategy，再刷新使用它的 case。
- 共享 `u32` 定义统一从 `lib/u32_def.v` 导出。
- 共享 `AFPoint`、`JPoint` 定义统一从 `lib/ecc_point_def.v` 导出；重复生成的
  case `_def.v` 只 `Require Export` 该共享文件。
- `SM2SIG`、`PrivKey` 的生成结构体定义统一从 `lib/sm2_protocol_def.v` 导出；
  `SM3_CTX` 的生成结构体定义与语义状态统一位于 `lib/sm3_def.v`。
- 归档验收以所有正式库、strategy goal check 和 89 个现有 C case 的
  `*_goal_check.v` 编译通过为准；`*_proof_auto.v` 是前端生成文件，不作为手工
  proof 完成度统计。

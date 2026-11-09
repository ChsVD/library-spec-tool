# 通用内容接入 QCP agent：问题与修正记录

日期：2026-10-20。对象：任意长度 `bn_add_words` 的 `r=a` 分支。本文保留早期阻点与修正过程；最新完成状态见下节。

环境后续已改名为 `runs/isolated-bn-words-sol61-high-20261020-01`，供 add、sub 及后续实验共用。本文可点击的当前文件链接已更新；历史说明中的旧目录名及历史运行内部的绝对路径保留原意。迁移不等于重新执行旧 run，后续验证须从新根目录正式初始化。

## 后续验证完成

新 run `bn_add_words-20261020181723` 已通过正式 `init-run` 接续当前 case，由新的 annotation owner 接入四个兼容引理的证明，保持 C 文件和原有引理声明不变。旧 run 的 blocked 状态与封存记录保留，不曾手工修改。

新 run 的 25 个顶层验证条件、7 个证明组全部正式 accepted；机械合并和 parent full verification 通过，`final-apply` 与 `final-check` 成功，随后 `step` 确认 `phase=done`、无 blocker、无待办 action。下文“0 组验收、返工路径不足”是旧 run 的历史状态；本次通过正式新 run 接续完成，而非实现了旧 run 自动恢复功能。

证明范围为默认 64 位、小端、非宽累加、四字展开加尾循环；正长度时 `r=a` 且 b 的 N 字资源与输出分离，排除 AllSame；N=0 允许任意指针。10 处直接 ULL 掩码适配保留。公共 `portable_sound`、`prefix_extend` 已用于实际证明；兼容 `bn_inplace_snapshot_finish` 用于最终结果的资源收尾。目标之外的别名/架构情况仍未验证，框架假设仍沿用既有环境。

- [正式状态](runs/isolated-bn-words-sol61-high-20261020-01/qcp/reports/bn_add_words-20261020181723/controller_state.json)
- [最终证明](runs/isolated-bn-words-sol61-high-20261020-01/qcp/Rocq/examples/IsolatedBnAddWords/bn_add_words_proof_manual.v)
- [最终辅助库](runs/isolated-bn-words-sol61-high-20261020-01/qcp/Rocq/examples/IsolatedBnAddWords/bn_add_words_lib.v)

## 为什么 Coq 编译通过仍会被拒绝

当前 QCP agent 的[禁用规则](runs/isolated-bn-words-sol61-high-20261020-01/qcp/.agents/skills/group-worker-proving/docs/forbidden-lemma.md)明确将 `entailer!` 列为禁用 tactic，理由是“隐藏闭合 goal 的实际步骤”；同时禁止裸 `pre_process` 和列出的 33 个 lemma。规则要求重写证明，不能改名、包装或注释绕过。

这是一项证明工作流的可检查性约束，不是 Coq 内核判定该 tactic 不可靠。`entailer!` 生成的证明可以通过 Coq，但不满足这套 agent 的证明文本规则。指定的 `LLM_pre_process`、`Goal_apply` 内部调用不受影响；允许的写法见[完整分离逻辑证明方法](runs/isolated-bn-words-sol61-high-20261020-01/qcp/.agents/skills/group-worker-proving/docs/separation-logic-whole-proof-tactics.md)。应显式组织资源匹配、纯事实和剩余目标，而非仅换一个自动闭合入口。

规则扫描组内 manual、辅助库、合并库和最终 case-lib。上游公共库也必须在交付前检查，否则可能直到证明阶段才暴露不兼容。

## 文件来源与责任边界

此前流程生成的数学库是 `runs/common-bn-add-words-independent-sol61-high-20261020-01/BnAddWords.v`。随后生成的 QCP 存储桥位于 `runs/common-bn-add-words-qcp-bridge-sol61-high-20261020-01/BnAddWordsQcp.v`，其证明包含多处 `entailer!`。

QCP annotation agent 在隔离环境中整理出 `qcp/Rocq/examples/IsolatedBnAddWords/bn_add_words_lib.v`。其中 `bn_expose_word`、`bn_rebuild_word`、`bn_inplace_snapshot_split` 和 `bn_inplace_snapshot_finish` 是对公共存储内容的具体适配，不是原封不动的公共库文件。当前失败发生在最后一个引理第 258 行：

```coq
rewrite UInt64Array.full_empty; entailer!.
```

因此既有上游缺少下游兼容性检查的问题，也有适配阶段未消除禁用写法的问题。

## 本次证明实验暴露的问题

1. **宏表达式的前端处理差异。** `BN_MASK2` 引用曾触发 `Integer literal is too large`；旧实验及本轮对照支持将相关引用展开为直接的 `0xffffffffffffffffULL`。不能据此声称 QCP 普遍不支持 64 位最大值。当前隔离源码已作局部适配，算法保持不变。
2. **指针等式不自动完成资源匹配。** 仅有纯事实 `r=a`，未必能让前端直接使用位于 `a` 的数组所有权完成 `r[0]` 写入。当前调整了局部指针存储和同基址数组区段表达。资源条件应写在分离逻辑规约与断言中；数学等式不能代替可写内存资源。
3. **旧输入事实在循环中丢失。** 原地覆盖后，当前数组的范围不能代替原始快照的范围。首轮检查在 `entail_wit_3_1` 中发现允许旧输入首字等于 `2^64` 的过弱前提。第二轮在活动循环不变量及相关断言中保留原始 A、D 的 bounded 与长度事实，未改变函数 Require/Ensure。这是标注缺口，不是 C 算法的反例。
4. **证明依赖工具配置必须一致。** 准备和后续 controller 调用的 Coq 工具环境不一致曾导致依赖快照失效。修复方式是保持工具路径与环境一致并重新准备，而不是绕过快照检查。
5. **公共库编译不等于 agent 兼容。** 当前公共存储桥通过过 Coq 检查，但禁用 tactic 未在交付前检查，导致 first_word 组在 Coq 编译之前被 group-safety 拒绝。
6. **受保护基础文件的返工路径不足。** 组内 worker 无权修改已封存的 seed；本次 controller 将错误登记为 `infrastructure / protected-seed-forbidden-tactic` 后没有返回 retry 动作。应支持返回 annotation 所有的 case-lib 修复、重新验证并封存依赖。尚未实现这条回退路径，不应人工修改 state 或已封存证明来假装恢复。

## 当前证明状态

隔离环境：`runs/isolated-bn-add-words-sol61-high-20261020-01`。运行：`bn_add_words-20261020120000`。

第二轮 annotation 与独立 VC checking 已接受，完整符号执行通过，共 25 个顶层验证条件、7 个待证明组。独立检查未发现确定的前提阻点，不等于证明这些条件成立。实际证明组验收数为 0，未完成最终合并与检查。

正式状态保存在 [controller_state.json](runs/isolated-bn-words-sol61-high-20261020-01/qcp/reports/bn_add_words-20261020120000/controller_state.json)。当前新公共库适配独立进行，不改该历史状态。

## 本轮适配与以后交付要求

新候选目录：`runs/common-bn-add-words-qcp-compatible-sol61-high-20261020-01`。保留旧产物，在新目录中重写存储桥证明，并提供上述四个局部适配引理的兼容版本。保持声明、前提、结论不变，不通过弱化结论、添加公理或包装禁用 tactic 通过检查。

交付需分别记录：

- 数学接口、数组长度、字宽、旧输入快照与所有权模式；哪些由纯数学库支持，哪些需要真实 QCP 资源。
- 对下游禁用项和适用证明结构规则的检查，以及所用规则版本/来源。
- 实际 Coq 编译、内核检查和关键引理的假设检查结果。
- 是否接入真实 case-lib、是否通过证明组验收、是否完成函数证明。独立库检查不能替代后三项。

本轮适配已完成，详见 [适配报告](runs/common-bn-add-words-qcp-compatible-sol61-high-20261020-01/REPORT.md) 与 [机器检查记录](runs/common-bn-add-words-qcp-compatible-sol61-high-20261020-01/compatibility-audit.json)。

27 个公共分离逻辑证明已改写；48 个公共 lemma 的声明以及全部非 proof token 不变，数学库逐字节不变。四个 case helper 的声明也保持相同，兼容替换版本保存在 `BnAddWordsCaseHelpers.v`。旧公共库的 17 处禁用项和旧 case helper 的 1 处命中均在新候选中消除，实际调用 QCP 扫描入口确认零命中，未新增 tactic 包装、占位证明或不安全假设。

数学库、公共存储桥、四个 case helper 及假设检查文件均已成功编译；三个交付模块通过 `coqchk -norec`，没有递归复核整个 QCP。纯数学主契约保持 `Closed under the global context`；分离逻辑引理仍依赖框架既有布局函数和外延性假设，完整结果保存在新目录 `assumptions.log`，不能把它们全部宣称为无公理证明。

此次仅完成独立公共库适配，没有修改旧 case-lib 或 controller 状态，也没有执行完整证明组的 seed、命名空间、分配路线及最终验收。后续应通过 annotation 修复轮次替换同名引理的 proof，重新检查与封存，不能在已有同名定义旁重复导入候选。受保护 seed 的正规返工路径仍待解决。

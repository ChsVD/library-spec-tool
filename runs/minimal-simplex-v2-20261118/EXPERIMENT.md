# Minimal Simplex v2 自然规约试验

## 输入

使用 example/minimal-simplex 中先前核对的冻结源码。入口为 `sx_check_qcp`。使用历史 Makefile 的原生 C 参数，编译数据库包含 58 个编译单元。顶层规范摘自 2026-11-13 生效的输入契约，范围限于顶层数学语义、所有权、输入域和执行环境。未向模型提供历史目标证明或辅助函数规约。来源、范围和摘要见 [输入来源](inputs/PROVENANCE.json)。

顶层规范要求正常返回的 0/1 精确对应有理可行性，归还原节点及系数头地址、数学值及可清理资源。旧验证模型为 QCP Arch32 BigEndian，本轮实际构图和链接证据采用 Linux x86-64 LP64。历史契约只能按其已验证模型解释，LP64 下的适用性仍需确认。

## 构图与复用证据

- [自动构图](stage1/stage1.json) 完成 58 个编译单元解析，得到 8 个入口可达函数。目标源文件通过自己的 backend.h 声明 MiniGMP 函数，调用解析得到唯一候选，但自动复用规则要求声明链能追溯到指定库路径，留下 37 个未确认调用点。
- [链接证据输入](stage1/link-evidence-stage1.json) 单独记录实验适配。使用相同 C 编译命令在临时目录生成对象，以 Clang 调用声明类型、nm 唯一的定义归属、可重定位链接解析核实 37 个调用点。它们归属于 10 个明确指定的 MiniGMP 函数，并形成 14 条直接复用边。重新计算范围后共有 19 个目标库函数，其中 11 个是通过 MiniGMP 访问的项目自有后端辅助函数。两份图保持独立，实验适配没有修改自动构图结果。
- [证据及契约区间](inputs/NATIVE_LINK_EVIDENCE.json) 对应各调用点。[MiniGMP 契约位置映射](inputs/reuse-contracts.json) 指向冻结 MiniGMP C 注释中的原文。GMP FME 作为普通参考。未调用 QCP，也未运行形式化证明。

## 自然规约输入和调用

本轮沿用 2026-11-02 版本的规范，规范摘要写在输入来源中。实际生成与审核使用 Codex CLI 0.166.0、gpt-6.1-sol、high 推理强度及 v2 自带的隔离后端。实验驱动通过原有只读 Reader 在每次生成和审核前交付完整的顶层规范摘录。链接证据驱动还预读公共声明与类型，减少重复读。模型运行事件仅保留阶段、目标函数与时间，规约和审核记录由 v2 写入 stage2.json。

已验证调用是程序按当前规约作出的自然语言审核结论，形式化调用验证状态为 `not_run`。

## 运行诊断与恢复

主试验保存 8/19 个结果后，malloc_gmp_div_inverse 的审核输出将外部 malloc（backend_alloc.c 第 24 行）标为 compatible。这条调用缺少程序认可的完整契约证据，校验器拒绝该标记并停止。相同输入、同一驱动和模型使用 --resume 后，该函数以 conditional 提交，继续后续任务。实验保留失败和恢复事件，未放宽校验器。

结果、进度和可读规约分别见 [JSON](stage2-link-evidence/stage2.json)、[汇总](RESULTS.md) 与 [逐函数规约](SPECS.md)。

同一问题随后在 free_gmp_div_inverse 的外部 free（backend_alloc.c 第 26 行）再次触发。当时已保存 13/19 个结果。保留该检查点和原日志，以 [源检查点及派生记录](CHECKPOINT_FORK.json) 续跑。在实验审核适配器中明确现有报告规则：audit_calls 中 incomplete=true 的条目只能写 unknown，或在有相反证据时写 conflict。提示变化只应用于后续审核请求，现有 13 份结果逐条验证未改动。派生检查点记录了新的驱动摘要和源检查点 SHA-256。v2 校验器、自有代码、调用图、契约及生成提示未变。第一次派生预检因遗漏传入原契约映射被 v2 拒绝，保留为 preflight-refused，无模型任务执行。

续跑结果在 [澄清后 JSON](stage2-link-evidence-clarified/stage2.json) 和 [续跑事件](stage2-link-evidence-clarified-events.jsonl)。汇总和逐函数规约显示最新检查点。

## 最终结果

主试验正常结束，工具状态为 partial。19 个待验证函数全部生成自然语言草稿并经独立审核，均为 conditional，其中 8 个属于入口核心，11 个是通过 MiniGMP 调用的项目自有辅助函数。原检查点中的 13 个结果逐项核对未变。

93 个调用点均有自然语言审核记录。42 个项目内部调用中 9 个 compatible、33 个 unknown。37 个 MiniGMP 复用调用和 14 个外部服务调用均为 unknown。主要待查事项为历史 Arch32 BigEndian 契约适配到当前 LP64 配置、资源定义与布局、分配及释放证据，以及项目自有后端调用者条件。自然语言阶段未自动新增调用边，形式化调用验证状态为 not_run。

模型交付 60 个公共内容需求，其中 21 个定义、19 个引理、20 个 strategy。主试验累计 81 次已完成真实模型请求（生成 44、审核 37），从首次请求到最后一次回复约 79 分钟，覆盖恢复和提示澄清的耗时。逐函数命名规约和未覆盖情形见 [可读规约](SPECS.md)，完整需求、审核、调用状态见 [最终 JSON](stage2-link-evidence-clarified/stage2.json)。

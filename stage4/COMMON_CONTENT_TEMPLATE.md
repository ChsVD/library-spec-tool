# 阶段三需求与公共内容规划模板

当前 schema 为 planning_policy=2。保持逐函数分析、整组合并、独立审查及有限修订流程，不新增模型轮次。产物仍是 JSON/Markdown 候选；Coq 生成与执行尚未接入。

## 需求分析

先理解任务情景，再按规约条款及实际使用位置识别需求。不强制十类检查，也不要求每个领域都生成数学表示、正确性和资源连接三层内容。

每个 needs 条目：

| 字段 | 含义 |
| --- | --- |
| id | 函数内稳定、唯一的需求 ID |
| spec_clause | 引用或准确定位上游规约条款 |
| use_site | 需要该内容的计算、证明或资源变换位置 |
| scope | shared / local / unknown |
| name / purpose | 名称与用途 |
| proposed_statement / assumptions | 精确需求及必要前提 |
| evidence | 实际读取的原文区间 |

analysis 说明情景、共享可能性及缺口。needs 可以为空，但要说明原因。categories 为可选的任务自定义提醒，若提供仍校验其状态和理由；不再要求固定类别。每函数只识别需求，整组选型避免重复建立基础模型。

## 参考追溯

common.references 每项包括 id、name、search_scope、applicability 和 facets。

facets 分别记录 definition、properties、boundaries、usage、environment；每个方面均有 status、reason、evidence：

- read：已读原文，必须提供本会话实际读取的证据。
- not_found：在所述范围未找到，不意味着不存在。
- not_applicable：与该用途无关，解释原因。
- unknown：尚未确认，保留影响。

这些是通用阅读问题，不是固定产物要求。数学定义不必有指针别名案例；资源谓词需要关注适用边界与实际使用。不能只摘取表面契约而遗漏相关定义和引理。可以只有一个候选，也可以没有适用参考；不能为凑比较数量编造来源。未读取的参考事实不能称为复用依据。

## 复用选择和覆盖

coverage 按函数映射。needs 保持原 common_needs 再接本轮 extract.needs 的顺序，以 index 追溯；本轮需求还在提取记录中保留稳定 id。

每项包含 action、reference_ids、item_ids、explanation、unresolved：

| action | 含义 |
| --- | --- |
| reuse | 直接使用已读的定义、谓词或引理 |
| adapt | 需要改变表示或接口 |
| supplement | 使用已有基础并补充缺失性质 |
| new | 确需新内容 |
| not_needed | 无需公共产物，解释原需求如何满足 |
| unknown | 未能确定，必须保留 unresolved |

reuse/adapt/supplement 要关联已读定义的参考。已复用的内容也列为 item，便于记录依赖和验证义务，并不要求重新生成该定义。not_needed 不映射产物。未解决需求不能通过独立审查；正常待执行的证明计划并非语义缺口。

items 保留 id、kind、name、parameters、assumptions、statement、purpose、origin、adaptation、evidence、used_by、depends_on、validation_plan、proof_status，并增加 validation_obligations。kind 支持 definition/representation/lemma/invariant/predicate。origin 仍是 source_fact/adapted/new_candidate，均不升级本轮证明状态。

多个需求可以共用一个 item；局部 helper 也合法。depends_on 指向本次条目且不能成环；外部依赖通过参考记录及原文说明。适配不能暗中缩小输入域，也不能把原地契约用作分离契约。

## 验证义务

每个 item 的 validation_obligations 为非空列表，每项有：

- id：该产物内唯一的义务 ID。
- kind：按实际用途命名，不受固定领域枚举限制。
- purpose：为什么需要检查。
- method：后续检查方法。
- environment：所需环境或待确认条件。
- success_criterion：判定满足义务的具体标准。
- status：planned / blocked / not_applicable。
- reason：blocked 和 not_applicable 必填。
- evidence：已有依据的原文区间，可为空。

当前只有规划，不能填 passed、executed 等执行结论。不能把所有义务都标为不适用。数学内容、引理、资源谓词和 QCP 连接按用途选择检查，不强制每项构造 C 调用。最小函数调用检查主要在后续形式化契约环节执行。Coq 编译不代表 QCP 实际可用，参考库结论不代表当前环境实测。

validation_plan 是上述义务的摘要。未来执行器应以候选版本和义务 ID 关联执行证据，不直接修改规划状态冒充实测；本轮未实现执行器。

## 输出与检查边界

planning.json 汇总 schema_version、needs、references、decisions、validation_obligations，并固定 execution_status=not_started、proof_status=not_proved。candidate.json 为完整候选，candidate.md 展示内容及结构化记录。

结构校验检查关联、字段、已读证据、状态和覆盖，无法判定数学结论真实或搜索充分。独立审查继续检查语义与适用性，pass 只表示候选可继续形式化。QCP auto_proof 不额外重复审查，不提取 strategy。

恢复身份绑定规划版本和提示摘要，旧阶段三输出不能直接作为新版完成结果恢复；请使用新目录。旧实验、证明文件及上游结果均不重写。

## 参考 strategy 附件（2026-11-02）

阶段四将选定参考定义/引理直接相关的 strategy 作为配套材料输出，不加入 C 使用示例，不生成新 strategy，不安装规则，也不执行目标适用性验证。

- candidate.json 新增 reference_strategies 列表；每条记录 id、reference_ids、source（path/start/end）、proof_sources、dependencies、applicability、target_status=not_validated。证明位置未找到时，proof_sources=[] 并填写 proof_unknown。
- items 新增 strategy_ids，通过 ID 关联规则。空列表表示没有附件；相关材料缺口仍应记录在 unknowns 或 adaptation。
- 程序从当前 Reader 允许访问的来源提取规则原文；生成者和通过审核的审查者均须实际读取规则和所引用的证明。源码包模式不回退到原库。
- reference_strategies/<规则ID>-<内容哈希>.strategies 保存选定行的原文内容，以 UTF-8、LF 和末尾换行保存。它不是可直接加载的完整策略包，不保证截取范围在语法或依赖上独立完整。
- reference_strategies/index.json 记录候选摘要、规则与候选项目关联、原始坐标和文件哈希、证明坐标和哈希、依赖及适用性说明。installed=false，target_status=not_validated。
- planning.json 保留附件来源记录；candidate.md 展示每项关联 ID。QCP agent 从 index.json 找到规则，判断直接复用、适配并重新证明，或仅借鉴。
- 修订后以最新 index.json 为准；旧的内容哈希文件可保留作历史记录，不得扫描目录把它们都当作当前附件。恢复已完成运行时检查候选摘要与附件哈希。
- 附件策略版本和提示摘要计入运行配置。旧运行不就地升级，使用新的输出目录；不修改旧实验或验收状态。

这些文件只是参考材料。对应证明存在、来源已读取，不代表规则已在目标库解析、加载、证明或运行成功。

## 分项审查与输入修订（2026-11-02）

--component-review 提供逐候选反馈和 retain/revise/add_material 动作。partial 仅表示部分设计通过审核，不能作为整体成功。--input-transition 与 --revise-from 在新目录记录精确新增文件清单，禁止修改旧输入；实际交付新增原文后修订候选并重新独立审核。输入转换和来源进入运行配置，strategy 附件同步更新。

具体字段、命令、输出和限制见 [分项反馈与输入修订](REVISION.md)。这两项属于现有生成—审核—修订循环。

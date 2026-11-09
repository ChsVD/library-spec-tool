> **适用范围**：本阶段面向一个待证明库和若干个已证明参考库。下文 OpenSSL BN、SM2、mini-GMP 及相关路径是当前案例；参考库数量不限定为两个。通用设计与当前实现限制见 [开发指南](../DEVELOPMENT.md)。

> **目录已按四阶段调整（2026-10-30）**：stage1 为模块分析，stage2 为函数图与范围选择，stage3 为自然语言规约，stage4 为通用定义和引理。阶段四使用 --stage3-run 指定自然规约目录，--stage2-run 仍作为兼容别名。历史运行内容不修改。完整流程见 [开发指南](../DEVELOPMENT.md)。

# 阶段四：公共定义与 lemma 候选

## 当前入口与输入

阶段四现在可以直接接收默认阶段三生成的自然语言参考稿：

    python3 -m stage4 --stage3-run runs/reference-specs --output runs/common-candidates

也可以在默认阶段三完成后自动衔接：

    python3 -m stage3 --manifest stage2/manifests/openssl-bn-module.json --output runs/reference-specs --with-common --common-output runs/common-candidates

未指定 --common-output 时使用阶段三输出目录加 -common。只有本次选定范围内所有函数都生成草稿后才启动阶段四；计划模式不启动，部分完成时自动衔接命令返回失败并保留阶段三结果。阶段三范围可以是选定的函数组或继续运行确定的下层范围，不代表整个库。

新版输入不要求完整源码包；默认阶段三已启用独立模型审核，启用审核的运行必须全部通过才能交接。显式 --skip-review 和历史未审核参考稿仍可读取，但不会伪造审核状态。程序检查草稿完成状态、目标覆盖、必要字段、输入快照及可用的图摘要，拒绝已标记失效的结果。旧版普通参考稿也可读取；旧版继续运行若没有记录最终目标范围，需先用阶段三原参数加 --skip-review --resume 补齐元数据。已有旧流程的已审查结果仍按原门槛读取，不降低其检查要求。

新版参考稿区分未审核 reference_drafts 和已通过独立模型审核 reviewed_reference_drafts，两者均未证明；阶段四公共候选审查通过不升级上游状态。不会修改上游运行文件。

## 生成过程

1. 每函数独立提取：读取自然规约和完整实现，从规约条款和实际使用位置提取需求，记录共享或局部用途；类别只作任务自定义提醒，不强制十类检查。新版没有 common_needs 字段时从 suggested_spec 提取，不能当作没有需求。计算接口、数学性质、等价连接及存储资源引理均在提取范围内。
2. 整组合并：按需读取逐函数产物和规约，生成定义、表示关系、lemma 与不变量候选。用 references 记录参考追溯，coverage 记录复用选择；每项保留参数、前提、精确陈述、来源、改造、依赖、适用函数和结构化验证义务。需求逐项映射，缺口保留为 unresolved，依赖不能成环。
3. 独立审查：重新读取候选、规约、目标实现和原文引用，检查覆盖、结论强度、前提、表示与边界。发现上游问题交回修订，不擅自改变前提。默认最多修订一轮。

模型通过 read/search/list/artifact 按需读取，不一次装入整个库。旧源码包输入仍只允许读取包内材料；新版直接从输入目录读取。没有新增参考方案比较器、自动分组或 Coq 生成流程。

新版 assumptions 原文以 reference-assumptions ID 进入继承条件，即使写“无新增假设”也保留原文。公共候选必须保留这些条件，审查逐项检查；未知调用、范围缺口和上游信任状态通过 upstream-context 提供给每个会话，并单独落盘。callee_requirements 仍只是调用需求，不能作为已证明保证。

## 输出与恢复

- functions/<id>/common_needs.json：逐函数需求、条款及使用位置。
- candidate.json、candidate.md：公共候选及覆盖映射。
- planning.json：汇总需求、参考、复用决定和验证义务；execution_status 固定为 not_started。
- review.json：公共候选的独立审查结果。
- upstream_context.json、upstream_conditions.json：上游类型、未知关系和继承条件。
- checkpoint.json、status.json、identity.json、input_snapshot.json：恢复、来源与一致性检查。
- tasks/、SUMMARY.md：会话记录和交接摘要。

--resume 复用完成的逐函数提取；上游、模型身份、规划版本或提示摘要改变时拒绝恢复。自动衔接时，阶段三 --resume 也会恢复已经存在的阶段四输出；若阶段四目录尚未创建则新建。已完成阶段四恢复不再调用模型。

阶段四每个角色任务默认最多 24 次调用、1800 秒、单次 600 秒、60000 上下文字符，候选报告最多 24000 字符。独立入口可用 --calls、--seconds、--call-timeout、--context-chars、--max-revisions 调整。自动衔接沿用模型与推理配置，阶段四使用自身默认预算；阶段三的审核修订次数、字符预算、无上限选项和单次超时不传给阶段四，需要定制阶段四预算时请分两次调用。

当前交付仍是 JSON/Markdown 数学与自然语言候选，全部 not_proved，不生成或编译 .v，不启动 QCP 证明。结构和来源检查不等于数学正确性检查，模型审查通过只表示可以继续形式化。新版衔接采用模拟模型做离线回归，尚未进行真实模型生成实验。

## 通用规划记录（2026-10-29）

[公共候选模板](COMMON_CONTENT_TEMPLATE.md)说明当前 planning_policy=2 的字段与规则。
从需求选择内容，不要求所有领域套用整数数组的检查清单，也不强制生成三个层次的产物。
参考阅读明确区分已读、未找到、不适用和未知；选择支持直接复用、适配、补充、新建、
无需公共内容和未知。验证义务按实际用途组织，当前只记录计划，禁止声称已执行或通过。

结构校验不等于语义证明，也不能自动判断检索充分。旧阶段四检查点不自动迁移，
使用新输出目录；阶段三历史输入的兼容性保持不变。
跨运行公共库管理、Coq 生成编译和 QCP 实际试用仍待后续开发。

## 多目标需求子图交接（2026-10-27）

阶段三使用 --scope-plan 时，整个需求子图的生成与所要求的审核必须完成，且范围摘要确认一致。阶段四对完整 target_ids 提取缺口和检查公共候选覆盖（新版计划包含自动补入的底层依赖）；上层 demand 规约、边界 context 和 boundary_edges 通过 upstream_context 作为未证明背景提供。目标假设与上层背景假设分开保存，不把上层前提直接施加给全部目标。没有 scope-plan 的既有运行保持原先全选定范围行为。详见 [函数组需求范围](../stage2/DEMAND_SCOPE.md)。


## 材料交付优化

当前入口已接入按任务筛选背景、自动交付必读材料及批量补读，具体协议、证据边界和兼容说明见 [材料交付](../MATERIAL_DELIVERY.md)。材料策略变化需要新运行目录，不直接迁移历史会话。

整体入口、代码结构和详细流程图见 [开发指南](../DEVELOPMENT.md)。

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

## 报告修复与重新校验（2026-11-02）

新增 --recover-from，在新目录复用停止任务的原报告、会话和已完成提取。先完整重新校验；仍有问题时，按错误补读或修订，再完整校验并继续独立审核。新增 --max-report-chars（正整数或 unlimited，默认 24000），提示与校验共用上限；不会自动放宽预算。格式错误保留原响应并有界修复。未接入输入修订及分项审查。

详细检查、命令和产物见 [报告恢复说明](RECOVERY.md)。共享执行器修改也影响阶段一、阶段二选择及其他调用方；完整回归不可省略。

## 分项审查与输入修订（2026-11-02）

--component-review 提供逐候选反馈和 retain/revise/add_material 动作。partial 仅表示部分设计通过审核，不能作为整体成功。--input-transition 与 --revise-from 在新目录记录精确新增文件清单，禁止修改旧输入；实际交付新增原文后修订候选并重新独立审核。输入转换和来源进入运行配置，strategy 附件同步更新。

具体字段、命令、输出和限制见 [分项反馈与输入修订](REVISION.md)。这两项属于现有生成—审核—修订循环。

# 开发历史记录

本文件保留 2026-10-30 整理前 DEVELOPMENT.md 的全部内容。以下“当前”“默认”“最新”均指各段写作时的状态，不能合并视为现行要求。现行架构、入口和维护规则统一见 [开发指南](DEVELOPMENT.md)。

---

> **2026-10-20 流程重写**：默认阶段二已改为“模块说明 + 原始函数实现 → 调用图/SCC → 自然语言推荐规约”。不再以源码提取、callee 规约就绪、独立语义审查或规约强度为门槛。推荐仅供参考，未证明。当前命令和完整流程以 [stage2/README.md](stage2/README.md) 为准；下文涉及源码包与审查的要求属于历史设计。旧入口为 `python -m stage2.legacy_cli`。

# 开发说明与运行记录

后续 BN 证明实验共用 `runs/isolated-bn-words-sol61-high-20261020-01`。该目录由原 add 隔离环境重命名，add 正式证明及封存历史保留；新实验从新路径初始化，不改写旧 run 内部的绝对路径。各 case 的准备状态与运行方式见该目录 README。

2026-10-20：`bn_add_words` 公共 Coq 内容接入 QCP 的问题与修正单独记于 [QCP_COMMON_INTEGRATION_NOTES.md](QCP_COMMON_INTEGRATION_NOTES.md)，包括宏展开、原地更新资源匹配、旧快照事实保持、禁用 tactic 和受保护辅助库的返工边界。

> 2026-10-20 当前流程：独立源码提取（每函数一个.c，含callee声明及已有QCP规约、宏和依赖）→人工审核/适配→固化版本→自然规约生成与审查。默认阶段2要求`--prepared-source`，不再自动提取或补包；callee规约缺失返回准备步骤，不读取其完整实现推断。命令与审核约定见[源码准备流程](SOURCE_BUNDLES.md)。下文涉及自动提取、自动补包的描述为历史设计。


> 2026-10-19 更新：默认采用[按函数源码包与独立规约子任务流程](SOURCE_BUNDLES.md)。源码提取后逐函数起草，不等待全组关系发现；阶段三也限定读取源码包。下文原库直接读取和全图先行调度描述仅适用于 legacy 历史流程。

已实现阶段 1 和阶段 2 首版。阶段 2 的函数图、局部会话、批调度与恢复见[stage2/README.md](stage2/README.md)，设计见[STAGE2_PLAN.md](STAGE2_PLAN.md)。本文原有运行记录保留阶段 1 的历史状态。

本次实现使用 Python 3.12 标准库，不需要安装依赖。新入口为 `python3 -m stage1.multi`；`python3 -m stage1.runner` 已转到同一流程，在本目录运行。该入口只运行阶段 1。阶段 2 使用 `python3 -m stage2`；两者均不执行 QCP 或策略提取。

默认无密钥启动：在已有 Codex 登录的 WSL 终端执行 `python3 -m stage1.multi --output runs/stage1-multi-first`。当前机器已验证 WSL 登录可用；桌面登录与 WSL 登录可能不同，详见下文。

## 已实现的能力

`stage1/reader.py` 提供 input 内的目录分页、字面搜索、分段文本读取。每次操作保存动作、返回内容、错误及截断信息。路径解析实际目标后检查边界，拒绝父级跳转、绝对路径和越界符号链接；不执行源码脚本、不修改 input、不联网补充资料。二进制、非 UTF-8、超过 8 MB 文件或单行超过 24000 字符均明确报告限制。

`stage1.multi`是默认CLI入口，调用`stage1/focused.py`的新流程：模块卡片与依赖图 → 依赖优先选择 → 职责/边界初筛 → 目标与match参考深读 → 逐对比较 → 逐对独立审查。每项都是独立模型会话，模型配置与原Codex隔离后端不变。全部主要模块都有轻量规划，但只给当前目标与初筛匹配参考派发详细说明任务；没有全量深读汇总前置任务。

`stage1/focused_contracts.py`检查依赖端点与原文、图上的候选、选择不越过先决条件、初筛逐项覆盖、比较不得改换目标以及独立审查引用。`stage1/task.py`新增角色动作白名单，初筛只能读职责/边界card产物，不能用Reader读取源码。普通角色继续使用原有Reader边界和证据机制。

`templates/focused-contracts.json`是新流程契约，`TASK_STAGE1_MULTI.md`提供共同规则。`stage1.multi.run_legacy_pipeline`及旧契约保留用于历史回归，不是默认CLI。旧`--max-rework-rounds`仅兼容解析，新流程在目标依赖冲突时保存结果并停止，尚未自动重划分或断点续跑。

依赖方向为dependent→prerequisite。程序不假设已有目标模块获证；调用、表示、规约依赖、未知和外部先决条件阻断初始候选，已确认构建边不决定证明次序。循环保留并报告。图只辅助选择，不代表完整调用图或可证性。具体流程与可信边界见[STAGE1_PLAN.md](STAGE1_PLAN.md)。

## 默认使用现有 Codex 登录

当前默认后端要求 Linux/WSL、`bwrap`、安装于 `/usr` 下的 Codex CLI（本机为 `/usr/local/bin/codex`），以及 WSL 用户 `~/.codex/auth.json` 中的现有 ChatGPT 登录。已在 `codex-cli 0.154.0` 上实测。无需 `STAGE1_API_URL`、`STAGE1_MODEL` 或 `STAGE1_API_KEY`。桌面或系统 keyring 中的登录不会自动复制进 WSL；若 WSL 尚未登录，应在正常 WSL 终端运行 `codex login`。

默认仅白名单读取现有 Codex 配置的 `model` 和 `model_reasoning_effort`，不继承其他用户配置。当前继承值为 `gpt-6-astra` / `low`，不是工具硬编码的模型选择；未配置模型时使用 CLI 默认值，也可显式传 `--model`。运行的 `model.json` 记录选择来源。

运行命令（WSL Ubuntu 内）：

```bash
cd /home/maxu/Projects/library-spec-tool
python3 -m unittest discover -s tests -v
python3 -m stage1.smoke --input input --output runs/codex-smoke-new
python3 -m stage1.multi --input input --output runs/stage1-multi-first \
  --calls 40 --seconds 1800 --call-timeout 600 --context-chars 120000 \
  --concurrency 2 --max-modules 24 --max-rework-rounds 1
```

`smoke` 只进行两轮真实调用：读取输入 README 的 1—12 行，再根据返回材料输出 checkpoint；不分析或推荐模块。新版阶段 1 使用 `multi` 命令（`runner` 是兼容入口），首次完整三库分析已尝试，因上下文预算耗尽而未形成报告，详见 TEST_RESULTS.md。

## Codex 后端的边界

每次调用在 bubblewrap 的临时最小文件系统中执行 `codex exec --ignore-user-config --ignore-rules --ephemeral --json`。不挂载 Projects、input 或真实用户 home；仅挂载 `/usr` 运行时、必要 TLS/DNS 文件和现有 auth 文件。auth 只读绑定，程序不读取、不复制、不解析凭据内容。若 CLI 需要刷新凭据但只读绑定阻止更新，程序会报告认证/刷新问题；请在正常 WSL 环境重新登录后重试。

隔离环境中的 home、cwd 和配置目录为空，因此原有 AGENTS、skills、插件和 MCP 配置不在文件系统中。另显式关闭 shell、网页、插件、apps、浏览器、子代理、code-mode host 等能力，设置空 MCP 配置和项目说明读取上限为零。原生工具事件检查只是额外诊断，不充当读取边界；项目文件没有挂载，实际阅读由外层 Reader 执行。工具不会因 bwrap 不可用而退回弱隔离。

子进程环境仅保留固定运行路径、临时 HOME/CODEX_HOME、TLS 配置和标准 HTTP(S) 代理/NO_PROXY 白名单；不继承原 OPENAI_BASE_URL、API 密钥、MCP 或任意 CODEX 环境覆盖。代理值不打印或写入日志。本机连接需要现有代理，去掉代理的第一次检查超时；保留后实际调用成功。CLI 必须联网使用已登录服务，因此这不是禁网沙箱。

超时或取消会终止并回收进程组，bwrap 配置 `--die-with-parent`；测试实际确认其新 session 中的父子进程均不会在超时后继续运行。只有最终 JSON 文本且收到 `turn.completed` 才接受结果；异常流或原生工具事件停止分析。CLI 0.154.0 关于已禁用 code-mode host 的已知 fail-closed 通知被单独识别，不当作工具调用。其他失败按连接、认证、限额、隔离和配置错误分类，不保存可能带凭据的原始 stderr。

后端每次把会话重新发送给一个新的非交互 CLI 进程，避免加载旧聊天或实验答案。长分析的性能和上下文预算仍待实际运行评估。

依据：[Codex 非交互模式](https://developers.openai.com/codex/noninteractive)、[认证](https://developers.openai.com/codex/auth)、[配置参考](https://developers.openai.com/codex/config-reference)，以及本机 `codex exec --help`、`codex features list`。文件隔离由本工具的 bwrap 配置和本机测试提供，不能仅归因于 Codex 的 read-only 模式。

## 显式 API 备选

只有希望改用兼容 Chat Completions 的服务时，才配置 `STAGE1_API_URL`（完整 HTTPS 地址）、`STAGE1_MODEL` 和 `STAGE1_API_KEY`，再添加 `--backend api`。服务需支持 `messages` 和 `response_format: json_object`。密钥仅从环境读取，不写入命令参数或文档。API 备选尚未用真实服务验证；不影响默认 Codex 后端。

## 任务预算及失败处理

输出目录必须是新目录，且在 input 之外；原始 input 不修改。修订后用新运行目录保留版本。默认**每个任务**最多 40 次调用、1800 秒、120000 上下文字符；不是全流程总预算。`--concurrency 2` 限制模块并行数，`--max-modules 24` 是计划模块上限，`--max-rework-rounds` 在新流程中仅兼容旧参数，不执行自动返工。总成本随模块数增加，目前没有全流程总费用预算或断点续跑。

每轮返回已用和剩余预算，默认预留 2 次调用、12000 字符、300 秒收尾，可分别通过 `--reserve-calls`、`--reserve-chars`、`--reserve-seconds` 调整。普通模型调用的超时额度也会扣除预留秒数；Codex 明确超时可转入收尾并计入调用次数，其他后端错误仍立即报告。进入收尾后禁止继续读取；如果一次材料反馈会占用收尾空间，完整反馈仅存审计文件，不交给模型，也不能作为已读引用。大报告本身仍可能越过硬上限并停止，预留并不保证一定完成。

每三个动作后要求提交非空理解草稿或报告；过程逐轮保存，不再依赖偶尔提交 checkpoint。报告结构修订最多两次（`--revisions`），失败原因区分调用、时间、上下文、校验或后端错误。预算耗尽时草稿仍可查阅，但不能当作正式完成。模型能力和真实源码规模仍可能导致理解不足。

## 输出与状态

- `plan.json/.md`：全库轻量模块卡片、覆盖与依赖依据。
- `dependency_graph.json/.md`、`dependency_frontier.json/.md`：图、可选候选、循环与阻断。
- `selection.json/.md`：跨库比较前提出的下一目标、范围与理由，尚未获批准。
- `screening.json/.md`：全部参考卡片的match/no_match/unknown及理由。
- `modules/<id>.json/.md`：本次目标与match参考的七项说明；JSON另含依赖复核状态。
- `comparisons/<reference-id>.json/.md`：逐对深入比较，可推翻初筛。
- `reviews/<task-id>.json/.md`：逐对独立审查，否决结果也保留。
- `tasks/<task-id>/`：独立会话、原文读取、草稿、候选报告、预算与状态。
- `final/report.json/.md`：仅全部本轮定向审查通过后生成，包含选择、初筛、比较、未决项和审查范围。不是全库详细报告。

顶层 `status.json` 区分 `pending_user_review`、`incomplete`、`needs_revision`、`input_changed`、`failed`、`interrupted`；具体预算和校验失败原因查对应任务。`user_approved` 始终为 false。真实调用使用 mode=`real_codex` 或 `real_api`；离线模拟运行成功为 `fixture_pipeline_complete`。运行模式只说明模型来源，**还必须核对输入快照**：真实 Codex 读取合成夹具成功不等于真实三库分析完成。

开始和完成时比较输入哈希快照，引用也核对读取时的哈希；不要在运行时修改 input。原始文件、模型解释、推荐候选和检查状态分别保留。planned_modules列出轻量规划模块；deep_read_modules只列本轮需详读的目标和match参考，completed_modules列出已完成详读任务。两者不能混淆，未读范围仍在规划coverage中。

用户审核至少抽查每个库、首选模块的入口和关键依赖、所有关键参考依据、领域知识来源与大小条件，还要检查覆盖报告中的未读区域。只有用户明确选择模块和范围后，才能人工记录审核决定并进入阶段 2；当前程序没有自动进入下一阶段的代码。

## 当前运行限制

默认 Codex 后端已通过两轮真实调用检查，记录位于 `runs/codex-smoke-20261018/`。读取的是 input/README.md 的小范围内容；没有生成 OpenSSL/SM2/mini-gmp 的模块划分或推荐。后续首次完整三库分析在 70 次调用后因上下文预算耗尽停止，未生成正式报告，语义质量和用户验收仍未完成，详见 TEST_RESULTS.md。当前只支持该 Linux/WSL 文件登录方式，不承诺所有桌面认证和 CLI 版本自动兼容。

## 测试范围

`tests/test_stage1.py` 使用独立临时夹具，覆盖读取边界、符号链接、分页截断、错误、证据是否已读和输入变化、栏目与链接、无法推荐、报告修订、预算与失败状态、输出位置以及 API 配置约束。夹具仅测试机制，不给真实库预设答案，不检查模型理解能力。

`tests/test_codex_backend.py` 另外覆盖模型配置白名单、最小环境、无项目挂载、原生能力关闭、完整事件流、脱敏诊断、真实 bwrap 可见性及超时子孙清理。后续完整运行仍需验证语义质量、整体阅读是否足够及推荐范围是否合适；API 备选兼容性也未验证。现有测试通过不能替代这些工作。

新版另有 `tests/test_multi_pipeline.py`，验证动态模块数、独立上下文、有界并行、失败保留、专门比较及审查、预算收尾和语义草稿、有界返工、派生材料与原始证据分离。合成输入 `tests/fixtures/multi-smoke/` 只用于真实调用的多角色交接检查，不包含真实三库源码或已证明内容。最新数量和运行结论以 TEST_RESULTS.md 为准。

多角色合成输入真实检查已完成：7个任务、55次真实调用，最终待用户审核。运行中修复的最终代码另经52项机制测试及历史材料校验回放，版本差异见 TEST_RESULTS.md；这不是对真实三库的全量验收。

## 指定本次运行的模型和推理强度

`--model gpt-6.1-sol --reasoning-effort high` 会显式应用于全部角色，覆盖本机配置中的模型与effort；不改写全局配置。每个任务的model.json记录实际传入值及explicit来源。此参数目前只适用于默认Codex后端；API备选会明确拒绝，避免悄悄忽略。新增覆盖优先级测试后53项测试通过。模型是否可用仍以实际服务调用为准。

参数依据：[Codex配置参考](https://learn.chatgpt.com/docs/config-file/config-reference)。

Sol 6.1真实测试使用并行安装的CLI 0.163.0：通过将`/usr/local/lib/stage1-codex-0.163.0/node_modules/.bin`置于本次命令PATH开头选用，原CLI不变。完整命令及实际失败结果见[runs/stage1-real-sol61-high-20261018-02/RUN_CONTEXT.md](runs/stage1-real-sol61-high-20261018-02/RUN_CONTEXT.md)。该轮接入成功但规划单次响应连续超过120秒，整库分析未完成；仅提高--seconds不能解除该历史版本每次调用120秒上限。

## 单次超时与中间文件保存（最新）

单次模型调用上限现为600秒，可通过`--call-timeout`独立调整；任务总时限默认1800秒，时间收尾预留默认300秒。正常调用取单次上限与“任务剩余时间减去收尾预留”的较小值，收尾调用取单次上限与任务剩余时间的较小值。因此总时间不足时仍可能少于600秒，不会越过任务总截止；固定120秒上限已移除。

各角色的中间输出存放在运行目录内，不使用系统会自动清理的临时文件夹：

- `tasks/<task-id>/draft.json`、`draft.md`：最新中间理解和任务状态，可直接阅读Markdown。
- `tasks/<task-id>/checkpoints/turn-XXXX-draft.json/.md`：每次非空草稿的独立版本。
- 同目录的`turn-XXXX-note.json/.md`和`turn-XXXX-report.json/.md`：检查点说明及候选完整报告，校验失败、超时或后续中断也保留。
- `tasks/<task-id>/report.json`：通过该角色结构与证据检查的报告。
- `modules/<module-id>.json/.md`：每个成功模块立即发布的说明，不等全部模块完成；某个模块失败时其他成功说明保留。

JSON和阶段Markdown先写同目录`.tmp`文件，刷新到磁盘后原子替换目标文件，减少中断造成半份文件的风险；草稿的历史轮次不覆盖。失败时不自动清理这些文件，不写入input。仍须区分草稿、角色检查通过、独立审查通过和用户批准；保存成功不等于内容正确。

模型任务说明要求尽早保存候选模块清单、已经形成的栏目及证据，避免全部留到最后一次大响应才提交。只能保存模型已经返回的内容；尚未返回的推理和响应不能靠这些文件恢复。**此次增加的是持久保存，不是自动断点续跑**；后续恢复仍需核验输入版本、原始阅读证据和任务状态，不能直接把未审查草稿当作完成结果。

使用Sol 6.1/high的下一轮命令示例（使用新运行目录）：

```bash
PATH=/usr/local/lib/stage1-codex-0.163.0/node_modules/.bin:/usr/local/bin:/usr/bin:/bin \
python3 -m stage1.multi --input input --output runs/stage1-real-sol61-high-next \
  --model gpt-6.1-sol --reasoning-effort high \
  --calls 50 --seconds 1800 --call-timeout 600 \
  --context-chars 160000 --reserve-calls 3 --reserve-chars 20000 \
  --reserve-seconds 300 --concurrency 3 --max-modules 24 --max-rework-rounds 1
```

59项机制测试通过；包含正常/收尾调用使用600或900秒配置、剩余时间限制、非法超时值、后端失败/中断保留版本、未通过报告不晋升为正式结果，以及原子替换失败保留原文件。未通过等待数分钟模拟耗时，测试直接检查传给后端的超时额度。尚未用这次修改重新运行真实三库。

## 依赖优先版测试

`tests/test_focused_pipeline.py`专门覆盖新默认流程。旧`tests/test_multi_pipeline.py`中的旧编排场景显式调用run_legacy_pipeline，继续保护历史行为和通用任务执行器；不能拿旧流程通过代替新流程测试。最新计数与结果见TEST_RESULTS.md。

上一版真实测试保留于runs/stage1-real-sol61-high-20261018-03。新版本尚未运行真实三库，未自动把旧24份说明转换为新依赖图或新推荐。继续采用新输出目录，避免覆盖历史证据。

## 已验证的受控续接（本次更新）

本次使用stage1.continue_saved复用旧24份模块说明：先核对完整输入快照、任务已接受状态、报告一致性，并从实际交付的conversation反馈回放原文哈希、文字和引用。未交付的withheld反馈不获得证据信用。补充图与后续比较使用独立任务；修订与恢复写入新目录，旧失败记录保留。

新增run_task的resume_from用于同角色、同提示、同模型/effort的已停止未完成任务；重新核对原文和已交付artifact内容后恢复对话，不把草稿自动当作有效结果。已完成或仍运行任务不能用此接口恢复。恢复任务的calls只计新增调用，previous_calls单独记录；续接入口按任务最多一次后端错误重试，消耗真实调用预算，默认普通任务仍不自动重试。

这是经本轮验证的受控旧产物续接，不是默认入口的任意状态自动恢复。CLI续接中的graph-checkpoint补充目前针对本轮mini-gmp两个缺口节点；downstream-from需要可核验的图修订来源。图的四条审查修订及规则补充另有runs目录内专门脚本及provenance，不应将这些专用步骤宣传为通用自动调度。

额外允许tentative的局部研究建议：必须列明具体scope、dependency_conditions和blockers，并核对原文；仅用于在整模块前沿为空时继续阶段1参考分析，不解除依赖、不批准证明。源码确认的构建边单独作为环境前置条件，不能因不参与证明排序就忽略。原图与说明、独立审查及最终构建前置清单见[续接总结](runs/stage1-continue-sol61-high-20261018-06/SUMMARY.md)。

85项机制测试通过，新增模型任务均使用gpt-6.1-sol/high。本轮实际复用了24份报告，未重跑模块worker；该轮完成时状态为pending_user_review，当时用户尚未批准阶段2。详细统计和审查修订历史保留在最终运行目录。

## 阶段 2 交接与开发设计（2026-10-18）

用户在上述运行完成后已认可首轮范围并要求进入下一阶段。采用非 `__e2k__` 的 `BN_num_bits_word` 通用 C 实现；环境与字宽条件仍须明确。历史 runs 文件保留当时状态，本节及 STAGE2_PLAN.md 记录当前决定。

开发改为直接复用已有模块说明和比较结论，结合目标实现、参考实现、已有规约及 Coq 内容起草自然规约，只围绕条款缺口补读。存在调用才向下展开，独立 agent 审查内容与原文依据，有限修订后交接自然规约和公共内容需求清单。具体输入、栏目、阅读范围、冲突处理、持久保存及首轮验收见[阶段 2 开发思路](STAGE2_PLAN.md)。

这次更新只修改文档。阶段 2 编排、规约生成与真实测试尚未执行；现有阶段 1 测试结果不代表阶段 2 通过。后续开发沿用现有 Codex 接入、Reader、快照与持久保存机制，模型继续采用 gpt-6.1-sol/high。

## 阶段 2 首版实现（后续更新）

已完成函数图、调用点需求、局部上下文、调用者优先调度、独立函数批处理、规约生成与独立审查、有限修订及受控恢复。直接复用阶段 1 的 Reader、任务预算、Codex 后端和检查点机制。图和规约不装入单个全库模型上下文，邻居规约变化会触发复查。运行入口、默认预算、输出位置及局限见[stage2/README.md](stage2/README.md)。

当前通过 108 项测试，其中新增阶段 2 测试 23 项。已核对 BN 首轮 manifest 与阶段 1 材料及输入快照一致；尚未运行真实 BN 自然规约生成，未执行 QCP。此前“仅修改文档”描述属于开发前的交接记录。

## 阶段二真实测试完成与修复

本轮单函数测试已完成，详细结果见[测试报告](runs/stage2-real-sol61-high-20261018-01/TEST_REPORT.md)。两次输出修订引起上下文超限后，复用图与草稿恢复，最终独立审查pass。上下文上限保持60000字符，全部角色为gpt-6.1-sol/high。

stage1.task新增可选allow_report_patch，默认关闭；阶段二开启后可用patch_report局部替换既有完整报告的顶层字段，合并结果重新完整校验并保存独立版本。阶段二恢复会交接明确标记的未接受旧稿，但不继承其原文证据信用。入边使用场景和出边调用需求分开存储，实际构建未知只能通过有解释、有条件引用的独立审查保留为条件候选，不能直接消除未知。

114项机制测试通过。真实测试只覆盖1个目标函数、4个上下文调用者；没有证明函数、没有执行QCP或自动进入阶段三。

## 2026-10-18：修正阶段 2 的选择单位

新增 `stage2/inventory.py` 与 v2 范围 manifest，默认从模块/函数组文件边界枚举全部定义。图保存预期成员；逐函数上下文与批调度保留，完成状态增加整组覆盖核对。预检写出文件覆盖及函数清单；解析缺口在模型调用前停止，旧手写清单需显式兼容参数。阶段 1 推荐提示同步要求完整范围。

130 项测试通过，覆盖批大小 1、独立成员、部分失败恢复、条件分支、范围缺口及身份重复。实际 `bn_word.c` 预检得到五个函数。本次没有重新进行真实模型生成；详见 [stage2 使用说明](stage2/README.md) 和 [预检清单](runs/stage2-bn-word-group-inventory-20261018-01/FUNCTION_INDEX.md)。

## 公共内容自动生成（2026-10-18）

新增阶段三：逐函数核对十类公共需求，合并生成定义、表示关系、lemma 和不变量候选，再独立审查并有限修订。`python3 -m stage2 ... --with-common` 在整组自然规约通过后自动继续；单独入口为 `python3 -m stage3 --stage2-run ... --output ...`。输入快照、整组覆盖和上游图状态不一致时拒绝交接，结果保留为未证明候选。设计见 [STAGE3_PLAN.md](STAGE3_PLAN.md)，用法与限制见 [stage3/README.md](stage3/README.md)。本次尚未进行 BN word 整组真实模型生成。

## BN word 整组真实测试（2026-10-18）

使用 gpt-6.1-sol/high 运行五函数自动链，完成两个关系报告，BN_add_word 首次及一次受控恢复均因后端连接错误停止。共记录 44 次调用；自然规约 0 份、阶段三未启动。输入未变化，中间结果均保留。前两个关系会话另暴露了较高上下文占用与未读依赖，不能把它们视为内容已验证。详见 [真实测试报告](runs/stage23-bn-word-real-sol61-high-20261018-01/TEST_REPORT.md)。

## 整组测试再次恢复

本次继续使用 Sol 6.1/high，新增 17 次调用，没有复现连接错误。BN_add_word 关系发现因阅读累计及两次校验修订达到 60192 字符，超过 60000 上限；最终草稿保留但未接受。自然规约和公共内容仍未生成。需改善调用者阅读拆分、已知函数身份复用及校验反馈，不能仅继续重跑。详见 [本次恢复报告](runs/stage23-bn-word-real-sol61-high-20261018-01/RESUME_2_REPORT.md)。


## 阶段二依赖图后端（2026-10-27）

当前 stage2 默认改用固定版本 FM-Agent C 后端，环境安装、源码副本、编译数据库、诊断及验证结果见 [FM-Agent 依赖图](stage2/FM_AGENT_GRAPH.md)。直接调用上游 CodeGraph/Clang/间接调用分析模块；旧词法实现保留为显式兼容选项。阶段一模块分析、规约审核及阶段三流程不因此替换。此处的构建配置只用于静态分析，不是正式 QCP 证明配置。

## 阶段二多目标需求范围（2026-10-27）

新增 stage2.demand_scope，直接消费已保存且身份一致的模块图；生成多目标 SCC 闭包、全部祖先或指定入口到目标的路径并集，独立保存需求节点和边界背景。阶段二新增计划摘要确认、精确边/调用点需求绑定；阶段三只把计划中的目标组作为公共内容工作项。完整用法及尚未实现的跨计划增量能力见 [需求范围说明](stage2/DEMAND_SCOPE.md)。实际 BN 示例仅完成静态规划，未运行模型或证明。

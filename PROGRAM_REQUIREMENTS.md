# 程序需求与接口

更新日期 2026-11-19。本文记录 v2 已实现的程序接口，供后续阶段使用。全局流程与尚待开发的内容见 [开发初稿](WHOLE_LIBRARY_DEVELOPMENT_DRAFT.md)。

## 阶段一 调用图与待证明范围

### 运行条件

首版面向 C。用户提供可编译的源码树、实际编译数据库及必要的生成文件。每个编译单元采用一套编译配置。如果实际构建失败，应先修复构建环境或输入，再启动阶段一。阶段一本身只运行图分析器和 Clang 语法分析，因此它报告的是分析结果。

从 v2 根目录执行 `bash scripts/setup_graph.sh` 安装固定版本的 FM-Agent、CodeGraph 及其 Python 环境。已有相同版本环境可通过 `--deps-root` 指定其所在目录。环境检查要求 FM-Agent 处于固定提交且受版本控制的文件无改动。

### 命令行

```bash
python3 -m stage1 \
  --target /path/to/target \
  --compile-commands /path/to/build/compile_commands.json \
  --configuration 'Linux x86_64 release' \
  --output runs/example
```

| 参数 | 合同 |
| --- | --- |
| `--target` | 目标源码根目录 |
| `--compile-commands` | 实际编译数据库，支持 `arguments` 或 POSIX 格式的 `command` |
| `--configuration` | 平台、架构及配置说明。编译参数来自数据库 |
| `--entry` | 可重复。支持唯一函数名、`相对路径:函数名` 或输出中的函数 ID。省略时选择配置范围内的全部待证明函数 |
| `--reuse-libraries` | 可选。指定已证明复用库的 JSON 文件 |
| `--output` | 尚不存在的运行目录，须位于所有输入源码树之外 |
| `--deps-root` | 可选。包含 `.deps` 与 `.venv-graph` 的目录。默认使用 v2 根目录 |

复用库配置示例。

```json
[
  {
    "id": "refmath",
    "root": "../refmath",
    "version": "v1.0",
    "compile_commands": "../refmath/build/compile_commands.json",
    "materials": ["../specs/refmath"]
  }
]
```

`id` 和 `root` 必填。ID 须唯一，以小写字母开头，可使用小写字母、数字、下划线和连字符。`target` 保留给待证明库。相对路径以配置文件目录为基准。允许将目标库内的子目录显式指定为复用库。

`version`、`compile_commands` 和 `materials` 可省略。目标项目的数据库已覆盖复用库编译单元时，直接使用对应记录。复用库编译单元由独立数据库描述时，提供该数据库以索引函数定义。只提供复用库目录时，可索引目标编译单元实际包含的复用头文件声明；复用库其余源码的覆盖情况见输出。`materials` 记录存在的契约、Rocq 文件或目录位置，供阶段二、三按需查找。

### 编译配置与复用判定

用户通过 `--target` 提供一份源码。阶段一在运行目录内自动建立一份供 CodeGraph、Clang 和后续阶段共用的快照；独立库的快照目录使用 `project/lib-<库ID>/`，嵌套的复用库沿用父库快照中的子目录。后续阶段按 `libraries[库ID].snapshot_root` 定位原文，旧运行仍使用各自记录的路径。程序重映射编译数据库中指向这些根目录的路径。数据库显式引用的外部头文件和构建目录仍可能需要原位置可访问。指向源码根之外的符号链接暂不支持。Clang 分析使用数据库的宏和头文件搜索路径，保留编译器系统头文件。分析范围以指定根目录中的 `.c` 编译单元及实际包含的头文件为准，当前版本针对常见的 Clang 兼容参数和项目布局。

阶段一按函数名、Clang 函数类型、链接属性和源码位置索引复用库。实际调用通过 Clang 声明链和目标定义归属确认。跨编译单元的复用定义要求有复用库声明来源和匹配的函数类型。只有已解析的复用库声明时，按用户提供的库及其构建配置建立声明边界。同名本地定义留在目标集，来源有歧义的调用保留为分析缺口。用户提供的复用库版本和当前构建配置应相互匹配，阶段二据此定位并检查对应契约。

### 输出契约

成功完成分析后，运行目录内的 `stage1.json` 是供阶段二读取的入口。当前 `schema_version` 为 1。

| 字段 | 含义 |
| --- | --- |
| `status` | `analysis_completed` 表示运行结束，且未报告影响所选范围的分析缺口。`partial_analysis` 表示存在解析失败或范围内分析缺口 |
| `configuration` | 用户提供的配置说明 |
| `libraries` | 按库 ID 索引。每项包含 `source_root`、相对于运行目录的 `snapshot_root`、可选版本信息及 `materials` |
| `graph.nodes` | 按函数 ID 索引。每项包含库、函数名、符号、类型、链接属性、源码位置、状态及 `selected` 标记 |
| `graph.edges` | 从调用者到被调用者的边。每条边有 `caller`、`callee` 和 `callsites`。调用点包含文件位置、类别和证据来源 |
| `graph.reuse_index` | 从成功解析的编译单元取得的复用库声明及定义，可按名称和类型查询 |
| `graph.external_calls`、`graph.analysis_gaps` | 全图已识别的外部调用与分析缺口 |
| `scope` | 范围选择、待证明函数 ID、复用边界、递归分量及分量依赖 |
| `coverage` | 编译单元解析状态、未纳入配置的源码清单、所选范围内的分析缺口和外部调用 |
| `provenance` | 后端版本、编译数据库与分析适配器摘要、分析副本文件摘要、原始构图文件位置 |

位置字段采用一基行号。`source` 对应函数定义的位置，具有 `path`、`line`、`column` 和包含末行的 `end_line`。已归属源码的路径相对于所属库根目录，Clang 未提供列号时为 0。调用点路径相对于调用方库根目录，库外声明可以记录绝对路径。函数 ID 由库、源码位置、符号和类型计算，绑定这次源码组织及配置。源码行号或类型发生变化后应重新读取 ID。

成功解析的定义附带 `translation_units`，列出看到该定义的编译单元。同一位置且同一类型的头文件定义会共用节点，并合并已识别的边。阶段二读取这类定义时应结合编译单元的参数检查宏差异。

函数状态为 `definition`、`reference_declaration` 或 `syntax_fallback`。最后一种来自编译单元解析失败时的旧版语法回退，类型可为空。调用点类别为 `direct`、`indirect_candidate` 或 `candidate`。候选边用于保守纳入可能的待证明目标，需结合 `analysis_gaps` 使用。旧版原始边、间接调用诊断和 Clang 错误保存在 `raw-graph.json`。其中的路径对应运行时的分析副本。

当调用点直接引用 Clang 标记为内建函数的隐式 `__builtin_*` 声明时，`graph.external_calls` 记录 `kind: "compiler_builtin"`、函数名、类型和调用位置。该记录的 `declaration_library` 和 `declaration` 均为 `null`。阶段二可以使用这条记录识别宏展开后的调用目标。

`scope` 字段如下。

| 字段 | 含义 |
| --- | --- |
| `mode`、`entry_ids` | `whole_library` 或 `entries`，以及已解析的入口 ID |
| `function_ids` | 阶段二应处理的目标函数 ID。全库模式包括无调用者的函数，入口模式沿已解析和候选调用边向下展开 |
| `reached_ids` | 范围遍历触及的函数，含为识别回调而查看的复用函数 |
| `reuse_boundaries` | 已识别的目标库到复用库调用边。callee 指向已有定义或复用声明 |
| `callback_dependencies` | 通过已知复用调用链回到目标库的依赖，用于调度 |
| `components`、`component_edges` | 待证明函数的强连通分量和分量间依赖。分量按调用者优先排列，边为 `[调用者分量 ID, 被调用者分量 ID]` |

阶段二从 `scope.function_ids` 和 `graph.nodes` 取得规约生成任务，通过 `libraries[节点库].snapshot_root / 节点.source.path` 读取函数原文。遇到 `reuse_boundaries` 时，按复用库、函数身份和配置定位其契约，检查调用处的前提和返回保证。已知回调继续纳入目标范围。存在 `partial_analysis` 时，阶段二应先检查缺口对当前函数及范围覆盖的影响。

命令行退出码为 0（分析完成）、2（部分分析，仍写出 `stage1.json`）、1（输入、环境或运行失败）。若失败发生在运行目录创建后，会写出 `failure.json` 并保留已有日志。命令行用法错误由 argparse 以退出码 2 报告，此时不会产生分析结果。调用方应同时检查 `stage1.json` 是否存在。

### 关键函数

| 实现 | 函数职责 |
| --- | --- |
| `stage1.pipeline.analyze` | Python 调用入口。接收与命令行对应的关键字参数，返回与 `stage1.json` 一致的字典，并写出运行文件 |
| `stage1.inputs.read_inputs`、`compilation_units` | 读取源码根和复用库说明，检查并合并编译数据库 |
| `stage1.inputs.prepare_snapshot` | 建立分析副本，重映射源码及编译命令 |
| `stage1.fm_graph_worker.main` | 调用沿用的 FM-Agent、CodeGraph 和 Clang 后端，保留原始边与解析记录 |
| `stage1.ast_records.collect` | 从成功解析的 Clang AST 取得函数声明、定义和直接调用证据 |
| `stage1.graph.build_graph` | 结合 AST 与旧版候选边建立函数身份，确认复用边界并记录外部调用和分析缺口 |
| `stage1.graph.compute_scope` | 按入口或全库模式计算范围，保留已知回调，按强连通分量组织待证明函数 |

Python 入口示例。

```python
from stage1.pipeline import analyze

result = analyze(
    target="/path/to/target",
    compile_commands="/path/to/build/compile_commands.json",
    configuration="Linux x86_64 release",
    entries=("main.c:entry",),
    reuse_libraries="/path/to/reuse.json",
    output="runs/example",
)
```

### 验收与限制

设置 `LST_RUN_GRAPH_TESTS=1` 后执行 `python3 -m unittest discover -s tests -v`。如使用外部已安装的固定后端，再设置 `LST_DEPS_ROOT`。测试覆盖多入口、共享依赖、递归、复用截断、同名本地函数、已知回调、头文件声明复用、条件编译、未知间接调用以及 GCC 可编译而 Clang 解析失败的情况。

函数指针沿用旧后端的候选分析，解析不全时记录缺口。只通过复用库头文件确认身份时，工具无法从未参与分析的复用库函数体中发现回调。库外显式依赖若未包含在分析副本内，其内容不受副本摘要覆盖。当前运行只反映指定编译配置下的静态分析结果。

## 阶段二 自然语言规约生成

阶段二读取阶段一的结果及源码副本。它沿调用者优先顺序处理待证明函数，单独处理普通函数，共同处理互递归函数。生成和独立审核使用 [规约书写规范](SPECIFICATION_WRITING_GUIDE.md)。

### 命令行与 Python 入口

```bash
python3 -m stage2 --stage1 runs/graph/stage1.json --output runs/specs
```

续跑时使用同一运行目录和输入，在原命令追加 `--resume`。阶段一目录须保留 `stage1.json` 和 `project/`。阶段二输出目录须位于阶段一目录和材料目录之外。

| 参数 | 用途 |
| --- | --- |
| `--stage1`、`--output` | 分别指定阶段一的 JSON 文件和阶段二运行目录 |
| `--reuse-contracts` | 可选 JSON 文件，按阶段一的复用函数 ID 定位既有契约 |
| `--background` | 可重复。提供背景、需求或领域知识文件或目录 |
| `--model`、`--reasoning-effort` | 传给沿用旧版实现的 Codex CLI 后端 |
| `--timeout`、`--context-chars`、`--max-revisions` | 分别为每次生成或审核会话的超时、字符预算和每组修订额度。默认为 600 秒、100000 字符和 1 轮 |
| `--resume` | 从已写入的结果继续处理 |

CLI 需要已登录的 Codex CLI 和旧版后端要求的 WSL 隔离环境。新运行在首次模型会话前保存初始状态。模型调用失败可在问题排除后续跑。同一目录由一个进程写入。Python 入口为 `stage2.pipeline.run`。它接受 `stage1_result`、`output`、`model_factory` 及上述可选输入，返回与 `stage2.json` 相同的字典。`model_factory(role, task_id)` 返回 `model(messages, timeout=...)`，角色为 `write` 或 `review`。

进程退出码 0 表示完成，2 表示有条件结果或受阻项，1 表示输入或运行失败，130 表示手动中断。参数用法错误也由 argparse 返回 2，可用 `stage2.json` 的存在和其中的状态区分。

### 复用契约与材料

复用契约映射示例。

```json
{
  "fn-实际使用的函数ID": {
    "path": "reference-contracts.c",
    "start": 12,
    "end": 21
  }
}
```

路径相对于映射文件，行号从 1 开始并包含末行。同一调用位置若对应多个可能目标，分别审核对应要求。已定位的复用契约原文随调用方任务交付。缺少映射的复用调用保留为待确认。阶段一登记的其他参考材料及 `--background` 输入可以通过只读工具按需使用。阶段二检查阶段一源码摘要，续跑时还比较背景、参考材料、契约配置、提示版本及模型设置。

### 交给阶段三的产物

`stage2.json` 是续跑文件和对外交付。当前 `schema_version` 为 1。

| 字段 | 含义 |
| --- | --- |
| `status` | `in_progress` 为尚有任务，`completed` 为范围内任务完成，`partial` 为留有条件结果、阻断或分析缺口 |
| `stage1_result`、`identity` | 阶段一入口位置和输入、材料及规则摘要 |
| `scope`、`accepted_edges` | 当前待证明范围及随规约审核接受的候选边。原阶段一图仍是基础数据 |
| `calls` | 按 `call_id` 查找调用者、候选目标、调用位置和类型 |
| `functions` | 按函数 ID 查找 `draft`、状态、审核依据 `reason`、未验证依赖和逐调用点 `call_checks` |
| `analysis_gaps`、`analysis_translation_failures` | 所选范围内带来的分析缺口和阶段一编译单元解析失败 |
| `external_materials` | 本轮引用的库外文件和已映射的复用契约文件，按材料别名记录实际路径与摘要 |
| `formal_call_validation` | 固定为 `not_run`，供后续 QCP 验证区分实际调用检查 |

`draft` 包含目的、符号、命名规约 `cases`、假设、未覆盖行为、出处、`call_requirements` 和 `common_needs`。严重缺少材料或达到预算的函数可只有受阻记录。阶段三导入有草稿的函数及其 `common_needs`，保留审核状态和未验证依赖，并记录缺少草稿的函数及原因。公共内容需求带有类别、使用位置、所需性质和阅读证据。证据的 `project/…` 路径相对于阶段一运行目录，其余别名通过 `external_materials` 查找原文。调用契约检查在相关审核中完成。跨分量的库内调用随被调用方审核保存，可用 `call_id` 关联调用方的要求。

### 实现位置与验收

| 实现 | 职责 |
| --- | --- |
| `stage2.pipeline.run`、`save` | 调度、续跑及原子替换结果文件 |
| `stage2.pipeline.run_task`、`audit_calls` | 生成、审核及各类调用点的检查安排 |
| `stage2.schedule.plan`、`task_description` | 合并已接受边、选择范围、构造任务输入和上层调用场景 |
| `stage2.materials.Materials`、`SourceReader` | 校验输入和证据区间；若返回的源码区间含待证明函数的定义起始行，`definitions` 给出函数 ID、名称、类型、行和列，供补边时引用 |
| `stage2.exchange.exchange`、`validate_draft`、`validate_review` | 只读工具交互、完成报告和审核结构校验 |

同组首审后，阶段二按函数计算返修次数。`--max-revisions 1` 表示每个函数在首次生成后最多再写一次。返修请求的 `task.members` 只列允许修改的函数；`previous_drafts` 携带它们的原稿，`previous_review` 携带对应的函数审核意见和调用检查结果。相邻函数的规约通过 `task.peer_contracts` 只读交付。独立审核复核修改过的函数和受影响的调用，其他草稿和调用结论保留。若只有调用关系被判冲突、审核未指定哪一方的规约有问题，则同批中仍有预算的相关端点可进入返修。

审核时，对于标有 `incomplete` 的调用，若模型报告 `compatible`，程序保留原意见（`reviewed_status`）并将有效结论记为 `unknown`。补边仍须独立审核通过才会进入调度，对于同一调用者、路径、行和列上的具名调用，若审核通过的目标唯一定义与缺口名称一致、有定义位置引用且无竞争记录，调度只生成一项内部调用要求。`calls[*].detail.resolved_stage1_gap` 保留对应的阶段一记录，`analysis_gaps` 仅列出仍待处理的缺口。间接调用的候选边继续保留缺口。

普通提交更新进度，接受新边时重算待证明范围。中断后重做尚未提交的函数或递归分量。阶段一调用缺口会随输出保留，新增候选边可用于扩大范围。

运行 `python3 -m unittest discover -s tests -v` 检查固定模型响应的生成调度、递归、复用冲突、补图与续跑。设置 `LST_RUN_GRAPH_TESTS=1` 及可选 `LST_DEPS_ROOT` 可同时启用真实阶段一构图及阶段间对接测试。

### C 标准库与编译器内建操作的增量规约表

维护目录为 [stage2/contracts](stage2/contracts/README.md)。阶段一提供 `compiler_builtin` 身份，阶段二按调用 ID、实际操作名和编译配置查表。默认表为空。普通外部函数和项目同名定义沿用既有流程。旧阶段一结果若将内建操作记为未解析调用，需用修复后的阶段一重新识别。

| 工具 | 可调用角色 | 输入与结果 |
|---|---|---|
| `lookup_contract` | 写作、审核 | 输入当前任务的 `call_id` 或 `call_ids`；命中时返回条目、操作、版本和规约正文摘要，同一批查询按正文去重。未命中区分缺少条目、配置不符和配置未知。 |
| `propose_contract_change` | 写作 | 输入已查询的调用 ID、基础版本、依据、理由和完整候选规约，返回提案 ID。修改时保留同条目内的已有操作。 |
| `review_contract_change` | 单独派发的规约表审核 | 审核者看到原文、候选正文、触发位置和配置，返回批准或退回及理由。批准时检查基础版本，退回时把意见送回写作者。 |

函数审核使用写作者最后查到的已批准版本。对该调用的检查结果保存 `contract_lookup`；命中时还保存 `contract`，含条目 ID、版本、摘要、操作和配置。审核人员逐个核对每个调用点的前提和效果，也需检查跨调用条件。未识别的接口或未查到适用规约时保留证据缺口。

每次运行在输出目录生成 `contract-changes.json`。其中 `approved_changes` 是实际批准数量，`events` 给出每项提案的新增或修改类型、基础和候选版本、正文前后对比、调用点、理由及最终状态。无提案时返回空列表。检查点保存日志路径和规约库位置，已完成的审核保留当时的版本。命令行的 `--contract-store` 可指定独立实验库。

## 阶段三 参考检索与公共内容生成

阶段三从阶段二的公共内容需求出发，读取目标函数、规约和调用点，检索相关的参考材料，生成并独立审核自然语言定义、引理和 strategy 建议。结果同时记录所用依据、适用条件和剩余证明义务。设计与验收情形见 [阶段三开发方案](STAGE3_DEVELOPMENT_PLAN.md)。

### 命令行

在 v2 根目录启动。生产 CLI 使用 Linux 或 WSL 下安装在 `/usr`（含 `/usr/local`）的 Codex CLI、可用的 `bwrap` 和基于 `~/.codex/auth.json` 的登录。模型通过临时会话接收输入和工具反馈，宿主执行受限的只读材料操作。

```bash
python3 -m stage3 \
  --stage2 runs/specs/stage2.json \
  --references reference-libraries.json \
  --output runs/common
```

| 参数 | 用途 |
| --- | --- |
| `--stage2` | 阶段二 `stage2.json`。需保留其绑定的阶段一文件、`project/` 源码副本和阶段二引用的其他文件 |
| `--stage1` | 可选。显式指定阶段一文件的位置，文件摘要须与阶段二记录一致。省略时使用 `stage1_result` |
| `--references` | 可选。参考库清单的 JSON 文件。省略时使用空参考索引，仍可按目标依据起草或记录缺口 |
| `--top-level-spec`、`--background` | 可选。分别提供一份顶层规约文件及可重复指定的背景文件或目录。阶段二已引用的材料按其原出处读取 |
| `--output`、`--resume` | 新建运行目录，或使用既有运行目录和匹配的输入续跑 |
| `--need-id`、`--max-needs` | 可重复选择已有的需求 ID，或限制本次处理的排队需求数。初次运行仍导入全部需求，可从输出的需求表取得 ID，再续跑选中的需求 |
| `--model`、`--reasoning-effort` | 默认 `gpt-6.2-sol` 和 `high` |
| `--timeout`、`--context-chars`、`--max-requests` | 默认每条需求跨生成、审核和修订共 600 秒、24 次模型请求，会话上下文预算为 100000 字符 |
| `--max-read-chars`、`--max-reads`、`--max-files` | 每条需求新读参考原文的字符、交付次数和不同文件数上限，默认分别为 60000、24、12。向独立审核转交已经读取的原文单独计入统计 |
| `--max-revisions` | 每条需求的修订轮次上限，默认 1 |

运行时在标准错误输出需求 ID 与处理状态，结束时在标准输出写出 JSON 摘要。退出码 1 表示输入或运行错误，130 表示手动中断。显式提供 `--need-id` 时，选中需求均为 `accepted` 返回 0，否则返回 2。省略 `--need-id` 时，运行状态为 `partial` 返回 2，`completed` 或因本次处理上限而处于 `in_progress` 返回 0。命令行用法错误也由 argparse 返回 2。

### 材料、索引与引用

参考库清单示例。

```json
{
  "libraries": [
    {
      "id": "resource-library",
      "role": "reference",
      "root": "../proofs",
      "files": ["theories/**/*.v", "qcp/*.strategies"],
      "version": "v1.0",
      "configuration": "QCP proof configuration"
    },
    {
      "id": "refmath",
      "role": "reuse",
      "root": "../refmath"
    }
  ]
}
```

也可直接提供库记录数组。`id` 和 `root` 必填，库 ID 唯一，相对根路径以清单所在目录为基准。`role` 默认为 `reference`。要按阶段一函数身份补查复用契约，使用 `reuse` 角色和相同的库 ID。`files` 可省略，指定时使用相对于库根目录的 POSIX 路径或 glob。省略时递归发现 `.c`、`.h`、`.v` 和 `.strategies`。显式指定的其他格式可作为文本文件检索。版本和配置随条目保存。

- 证据读取使用阶段一源码清单和摘要定位函数原文及编译参数，按阶段二材料别名还原已引用的背景和契约。调用条件和检查通过 `call_id` 关联，保留检查保存方，多个调用位置各有记录。复用契约按实际被调函数的库和路径及阶段二为该函数显式绑定的区间定位，保留命名分支。索引中同路径但摘要不同的复用契约是版本待核对的候选。
- C 索引记录函数声明及 QCP 命名契约、`With`、`Require`、`Ensure` 和 Coq 指令。Rocq 索引记录声明、可识别的参数和逻辑结构、导入关系及单独的证明体区间，可标出部分生成验证材料。strategy 索引记录多行规则的编号、左右侧、检查和动作。无法识别的结构保留出处。
- 生成和审核通过 `list_files`、`search_references`、`list_entries` 和 `related_entries` 查候选，通过 `read_entry` 读取原文，通过 `list_sources`、`read_source` 查目标与背景材料，并可通过 `shared_items` 查已经审核的内容。搜索支持 `text`、`objects`、`have`、`need`、`symbols` 和 `kind`，也可按文件、库或角色限缩范围。`related_entries` 返回显式符号、导入、契约和证明关系的线索，保留歧义候选。
- 原文引用采用条目 ID、路径、从 1 起算且包含末行的 `start_line`、`end_line` 和 `file_sha256`。参考路径相对于对应库根，目标证据使用运行材料别名。程序校验引用是否在本次会话实际交付，独立审核以正文和原文检查方向、目标条件、依赖和内容。

### 输出和续跑

生产运行输出 `stage3.json` 和 `stage3.md`。JSON 采用 `schema_version: 2` 和 `mode: "production"`，是续跑与下游读取入口。Markdown 在本次运行结束时从 JSON 导出。

| 字段 | 含义 |
| --- | --- |
| `identity` | 阶段一和阶段二文件、目标证据清单、参考库文件与索引版本、提示词、模型和处理预算的身份信息 |
| `needs` | 按需求 ID 索引。ID 由函数 ID、需求顺序及原始内容摘要生成。每条保留阶段二的原始需求 `kind/use/need/evidence`、规约状态、审核原因、未验证依赖、相关调用和冲突调用 ID |
| `blocked_functions` | 无草稿或尚未产出阶段二草稿的函数、调用和原因。有草稿的冲突需求仍保留在 `needs` 中 |
| `items` | 已审核的共享定义、引理和 strategy。条目有类别、标题、正文、参考原文 ID、依赖及由内容生成的 ID。同一条目可被多处使用 |
| `uses` | 按需求 ID 索引，保留处理状态、关联的共享条目、调用点、对象对应、使用条件、剩余义务、引用、搜索范围、审核意见和会话用量。尚待处理的需求只出现在 `needs` 中 |
| `sources` | 按证据 ID 索引的原文和出处，供核对已引用的证据与审核发现 |
| `status`、`summary` | 运行状态与需求、覆盖、共享条目和用量统计。`in_progress` 表示有待处理需求，`partial` 表示已记录待复核项、可重试受阻项或无可用草稿的函数，`completed` 表示导入需求均已审核结案且无受阻函数 |

`uses[need_id].status` 为 `accepted`、`needs_review` 或 `retryable`。审核可以接受有具体说明的缺口。`coverage` 为 `complete`、`partial` 或 `uncovered`。`disposition` 为 `direct_reference`、`adaptation`、`inspiration`、`new_content` 或 `gap`。`applicability` 保留阶段二的冲突或条件，取值为 `blocked_upstream`、`conditional_upstream` 或 `requires_target_validation`。每个用途的 `target_validation` 为 `not_run`。Rocq 和 QCP 的目标验证留给后续阶段。

程序按需求原子保存 JSON。每个运行目录同一时刻只允许一个写进程。修订额度用尽后保留未提交稿和审核意见。模型或交互受阻、可恢复的读取失败会记录原因和可重试状态。追加 `--resume` 处理尚未开始的需求及 `retryable` 记录，跳过已审核结果和待人工复核的稿件。续跑核验输入和处理设置；对于已经接受的需求，还按文件复核生成和审核曾收到的目标材料以及编译配置的 SHA-256。允许调整本次超时、需求选择与处理数。若绑定源码暂时不可用，可在恢复原始文件后续跑；有意修改输入材料时使用新运行目录。

输入较长时，模型可用 `list_context` 和 `read_context` 分页定位、读取调用记录、复用契约、相关函数与目标证据。修订时可沿用已读原文及审核意见所引的原文。审核与修订中的原文转交单独计数，不重复消耗新读额度。

### Python 接口与实现位置

| 实现 | 职责 |
| --- | --- |
| `stage3.pipeline.run` | 生产入口。接受 `stage2_result`、`output`、`model_factory`、可选 `stage1_result`、`reference_manifest`、`top_level_spec`、`background`、`resume`、`need_ids`、`max_needs`、`limits`、`model_identity` 和 `progress`，返回与 `stage3.json` 相同的字典 |
| `stage3.evidence.load_evidence`、`Evidence.for_need` | 核验阶段一身份、导入需求、按调用和来源交付目标证据及读取错误 |
| `stage3.index.build_index`、`ReferenceIndex` | 从清单或内存库记录建立索引，实现查询、读取原文、按实际路径查契约及查关联线索 |
| `stage3.index_formats.parse_c`、`parse_rocq`、`parse_strategies` | 按格式提取条目、结构、来源区间和显式关联 |
| `stage3.exchange.Limits`、`ReadTools`、`exchange` | 处理交互额度、只读操作和每轮实际交付的原文 |
| `stage3.pipeline.run_need`、`stage3.reports.validate_draft`、`validate_review`、`commit_items` | 组织生成、独立审核和修订，校验引用、调用归属及条目依赖，提交共享条目 |
| `stage3.model.Stage3CodexModel`、`stage3.export.write_markdown` | 实现 CLI 使用的 Codex 模型后端及可读报告导出 |

`model_factory(role, need_id)` 返回 `model(messages, timeout=...)`，角色为 `write` 或 `review`，可注入固定响应运行测试。`progress(need_id, status)` 接收需求开始和保存后的状态。执行 `python3 -m unittest discover -s tests -v` 可运行当前阶段三的取证、索引、审核校验和续跑回归。

### 离线验收入口

`python3 -m stage3 --stage2 STAGE2_JSON --reference ROCQ_FILE --fixture REVIEW_JSON --output STAGE3_JSON` 保留单文件、固定查询和固定审核响应的回归入口。`--reference` 与 `--fixture` 必须成对使用，`--output` 指向一个尚不存在的 JSON 文件。该入口生成 `schema_version: 1` 和 `mode: "offline_fixed_review_fixture"` 的独立结果，含阶段二摘要、原需求和调用条件、方向排序、已交付原文、固定审核和逐用途中保留的缺口。冻结输入、数组方向排名与结果判定见 [阶段三离线验收](STAGE3_OFFLINE_ACCEPTANCE.md)。

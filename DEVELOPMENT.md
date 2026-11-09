# library-spec-tool 开发指南

更新时间：2026-10-30。本文以当前代码入口和交接校验为依据，作为项目结构、流程与维护工作的统一入口。它描述工具当前能做什么，不把历史实验成功等同于默认工具已经自动实现。

项目根目录：

- WSL：`/home/maxu/Projects/library-spec-tool`。
- Windows：`\\wsl.localhost\Ubuntu-24.04\home\maxu\Projects\library-spec-tool`。
- 运行环境：Ubuntu-24.04 WSL；命令示例均在项目根目录的 Linux shell 执行。
- 开始工作前检查目录层级内适用的 `AGENTS.md`。不要修改历史实验的验收或封存文件。

## 阶段编号与代码目录的对应关系

本文统一使用以下四个阶段。**代码目录和默认命令已经按四阶段划分。** `stage1/` 至 `stage4/` 分别对应阶段一至四；历史运行目录和文件内容不迁移。

| 流程阶段 | 工作内容 | 当前实现位置 |
| --- | --- | --- |
| 阶段一 | 划分和比较模块，推荐当前最适合处理的目标模块及参考模块，由用户确认 | `stage1/focused.py` |
| 阶段二 | 为选定模块构建函数依赖图，选择当前最适合处理的一批函数，并确定所需的调用者、被调用者和处理边界 | `stage2/fm_graph.py`、`inventory.py`、`select.py`、`selection_tools.py`、`demand_scope.py` |
| 阶段三 | 根据调用关系，自顶向下为本批函数生成自然语言规约，汇总多个调用者的需求，并审核规约 | `stage3/reference.py`、`reference_review.py` |
| 阶段四 | 根据本批函数规约，生成可复用的通用定义和引理 | `stage4/pipeline.py`、`planning.py`；目前只实现需求分析、候选设计和审核，Coq 文件生成与验证尚未接入 |

阶段二可人工指定初始函数组，也可使用 stage2.select：同一 agent 阅读背景和实现，沿图向上提出函数组；静态工具计算新增依赖、材料大小和批次上限。结果仍等待用户确认，不保证全局最优。详见 [函数组选择](stage2/SELECTION.md)。

### 术语约定

| 术语 | 本文含义 |
| --- | --- |
| 函数依赖图（当前主要是调用图） | 节点是具体函数定义，边从调用者指向被调用者。当前图还记录无法确定目标的调用；不能当作完整的全程序依赖分析结果 |
| 强连通分量（SCC） | 图中相互可达的一组节点；递归或相互递归函数需要按分量组织 |
| 前置条件 / 后置条件 | 分别描述调用前必须满足的条件、返回后保证成立的性质。QCP 中包含分离逻辑的内存断言 |
| 分离逻辑的空间合取 `P * Q` | 表示两部分可分离的内存资源分别满足 P 和 Q；`emp` 表示空内存资源 |
| 函数契约 | 函数的前置条件、后置条件及相关逻辑参数；自然语言推荐规约不等于已验证契约 |
| 验证义务（proof/validation obligation） | 为确认定义、引理或适配方案可用而必须完成的检查或证明；记录义务不表示已完成 |
| 输入快照 / 内容摘要 | 输入文件的版本记录及其哈希，用于检测文件变化；不是形式化证明 |
| manifest（输入清单） | 指定模块、源文件范围、配置和参考材料来源的 JSON 文件 |
| 候选 | 已提出但尚未完成所需形式化验证的定义、引理或规约 |
| target / demand / context | 代码中的范围分类：本批处理目标、为推导需求而分析的上层调用者、仅供参考的范围外函数。详细集合见阶段二 |

## 阅读导航与维护约定

| 想了解什么 | 阅读位置 |
| --- | --- |
| 工具目标、实现边界 | 本文“当前能力”和“整体流程” |
| 阶段一模块分析 | 本文“阶段一”；[阶段一设计](STAGE1_PLAN.md) |
| 函数图与环境 | 本文“构建函数图”；[FM-Agent 后端](stage2/FM_AGENT_GRAPH.md) |
| 函数组选取、上下游范围 | 本文“范围规划”；[范围协议](stage2/DEMAND_SCOPE.md) |
| 自然规约与审核 | 本文“阶段三”；[自然规约入口](stage3/README.md)、[自然规约模板](stage3/NATURAL_SPEC_TEMPLATE.md) |
| 材料准备、预算、批量读取 | 本文“任务输入准备与读取”；[材料协议](MATERIAL_DELIVERY.md) |
| 通用定义和引理规划 | 本文“阶段四”；[通用定义与引理入口](stage4/README.md)、[通用定义和引理候选模板](stage4/COMMON_CONTENT_TEMPLATE.md) |
| 独立源码准备与历史兼容 | 本文“入口与代码导航”；[源码准备](SOURCE_BUNDLES.md) |
| 优化意图、实验教训 | [优化依据](TOOL_OPTIMIZATION.md)、[QCP 集成记录](QCP_COMMON_INTEGRATION_NOTES.md) |
| 历史开发过程 | [开发历史](DEVELOPMENT_HISTORY.md)；`runs/` 中相应报告 |

**如何保持本文有效：**

1. 改变入口、阶段顺序、输入输出、状态或已验证与未验证结果的区分时，同步更新本文相应段落和流程图。
2. 字段与命令细节维护在阶段文档中；本文维护整体结构，并链接到具体实现，避免把同一大段说明复制到多个文件。
3. 图中实线表示当前实现内的处理或交接；虚线表示人工协调、兼容支线或待开发步骤。节点上的“静态”“模型”“人工”说明责任归属，不表示正确性等级。
4. 记录变化时区分“代码已实现”“测试替身验证”“真实模型试运行”“当前环境正式验证”。不得互相替代。
5. 历史运行目录只追加必要说明，不改写原输入、运行配置、输出或验收状态。策略变化使用新运行目录。
6. 本文与代码不一致时，先检查默认 CLI、`identity.json` 和校验逻辑，再更正文档；不要为符合旧文字恢复旧流程。

## 1. 工具目标与当前能力

工具面向一个待证明库和若干个已证明参考库，通过分析待证明库的实现和参考库已有的规约、定义、引理及证明，辅助生成自然语言规约、可复用的通用定义和引理，并交给 Coq/QCP 进行验证。工具采用分阶段、按需读取、保存中间结果的方式，不是一次把所有源码交给模型完成证明。

| 能力 | 当前实现 | 不能据此声称 |
| --- | --- | --- |
| 模块划分、依赖规划、分层跨库比较 | 阶段一已实现；选择结果仍待人工确认 | 整个目标库已分析完整或已完成证明 |
| 函数图 | 默认固定版本 FM-Agent C 后端，保留配置、候选边和未知项 | 函数指针、宏和全部平台配置均已解析 |
| 函数组范围 | version=2 向下补依赖，再向上汇总需求；支持显式边界 | 图上的叶子必然没有真实依赖 |
| 自然规约 | 默认生成、独立模型审核和限制次数的修订；支持领域关注点 | 模型 pass 等于语义证明 |
| 材料准备 | 静态定位类型/宏候选；任务相关背景；自动交付必读材料；批量补读 | 已完成 C 预处理或全部递归引用的类型定义 |
| 阶段四 | 逐函数需求提取、汇总本批函数需求、参考追溯、复用选择、验证义务和独立审核 | 已生成、编译或验证 Coq 文件 |
| 独立源码准备 | 另有提取、人工适配/确认和旧源码包流程 | 它是当前自然规约入口的必要前置步骤 |
| Coq、形式化规约、spec_check、调用检查、QCP 证明 | 有独立实验和人工协调证据；尚未接成默认完整自动链 | 整体工具已自动从模块走到证明验收 |

当前默认自动交接的终点是**阶段四通用定义与引理的候选设计**：`proof_status=not_proved`、`execution_status=not_started`。暂不开发 strategy 自动提取。

### 通用输入模型与当前案例

- **待证明库：** 本轮需要分析和验证的一个软件库，包括源码、头文件、构建配置和已有需求说明。
- **已证明参考库：** 若干个可供比较和复用的软件库，每个库分别提供实现、已验证规约、定义、引理和证明材料，并记录证明覆盖范围、配置及假设。称为“已证明库”不表示其中所有模块和所有配置均已验证。
- **选择关系：** 每个目标模块可以匹配零个、一个或多个参考模块；不同目标模块不必使用同一参考库。没有适用参考时应记录结果，不能强行建立对应关系。
- **当前案例：** OpenSSL 是待证明库，SM2 和 mini-GMP 是已证明参考库。本文的 BN 命令和实验数据用于说明当前案例，不限定工具只能处理这些库或只能接收两个参考库。

**实现限制：** 当前阶段一仍将这些案例名称用于库标识校验和目标库判断，例如 stage1/contracts.py 的库集合校验、stage1/focused.py 和 focused_contracts.py 对 openssl 的判断。因此，“一个待证明库和若干个已证明参考库”是工具的通用设计；任意库集合的配置支持尚未完全实现。后续需要将目标库角色、参考库列表及材料路径改为输入配置，本次只修正文档，不修改运行逻辑。

### 整体流程

```mermaid
flowchart TD
    IN["输入：一个待证明库的源码；若干已证明参考库的源码、规约和证明材料"] --> S1["阶段一：模块划分、比较与选择"]
    S1 --> O1["输出：模块职责与源文件范围；模块依赖；参考模块适用性；推荐目标模块"]
    O1 --> H1{"用户确认目标模块和参考模块"}
    H1 --> S2["阶段二：构建函数依赖图并确定本批函数"]
    REQ["人工指定初始函数组<br/>可选调用入口及排除依赖的理由"] --> S2
    READ["可选：一个 agent 阅读背景和实现<br/>通过静态工具查询依赖增量、材料大小和上限"] --> S2
    S2 --> O2["输出：函数与调用点；未解析调用；本批目标函数；需求调用者；范围边界；处理顺序"]
    O2 --> H2{"用户确认本批函数及边界"}
    H2 --> S3["阶段三：自顶向下生成自然语言规约并审核"]
    O1 --> S3
    S3 --> O3["输出：每函数逻辑参数、前置条件、后置条件；传给被调用者的需求；假设与未知项；审核结果"]
    O3 --> G{"范围内生成和审核完成；输入版本一致"}
    G -->|否| STOP["保留已生成结果和问题记录"]
    G -->|是| S4["阶段四：生成通用定义和引理"]
    IN --> S4
    S4 --> O4["当前输出：需求清单；候选定义与引理的陈述；参考来源；复用选择；待执行的验证义务；审核结果"]
    O4 -.-> V["待开发：生成 Coq .v 文件，编译、证明并检查 QCP 适用性"]
    V -.-> Q["后续：形式化函数规约、最小调用测试、QCP 函数体证明"]
```

实线表示当前已有的处理或人工确认步骤；虚线表示尚未接入的执行步骤。阶段四的目标产物是 Coq 定义和引理，但当前自动流程仅输出候选设计及验证计划。

当前 `python3 -m stage2` 只构建函数图；`python3 -m stage2.demand_scope` 计算函数范围；`python3 -m stage3` 生成自然规约，也保留 `--prepare-only` 用于生成前的静态准备。`--with-common` 在阶段三完成后调用现有 `stage3` 包执行阶段四，不会自动开始 Coq 或 QCP 证明。

## 2. 入口与代码导航

### 2.1 当前入口和兼容入口

| 入口 | 调用实现 | 用途 |
| --- | --- | --- |
| `python3 -m stage1.multi` | `stage1/focused.py` | 当前模块分析、初筛、深读、比较和独立审核 |
| `python3 -m stage1.runner` | CLI 转到 `stage1.multi` | 兼容命令；文件内仍留有旧 runner 函数 |
| `python3 -m stage2` | `stage2/__main__.py` | 静态构建函数图，不调用模型 |
| `python3 -m stage3` | `stage3/__main__.py → reference.main` | 自然规约生成与独立审核 |
| `python3 -m stage2.select` | `stage2/select.py → selection_tools.py` | 一个模型会话读取原文并选择函数组；静态工具计算依赖、材料与上限 |
| `python3 -m stage2.demand_scope` | `stage2/demand_scope.py` | 阶段二：根据函数请求计算处理范围；不运行模型 |
| `python3 -m stage4` | `stage4/__main__.py → pipeline.run_pipeline` | 通用定义和引理候选规划 |
| `python3 -m stage2.prepare extract / approve` | `stage2/prepare.py` | 独立源码提取与人工确认；不是默认自然规约前置步骤 |
| `python3 -m stage2.legacy_cli` | `bundles / legacy` 分支 | 兼容旧源码包、旧规约流程；不能当作当前默认入口 |
| `runs/.../native_driver.py` 等 | 单轮试验适配器 | Windows 原生子 agent 等实验接入，不是已产品化的默认后端 |

尤其注意：`stage2/pipeline.py` 仍被复用来加载 manifest，但它自己的旧流程不等于 `python -m stage3` 的当前执行流程。

### 2.2 目录职责

| 目录或文件 | 职责与维护重点 |
| --- | --- |
| `input/` | 原始库及参考材料副本；模型读取边界，不存生成结果 |
| `stage1/` | 模块分析，同时承载 Reader、任务执行器、后端、快照等公共基础设施 |
| `stage2/` | 函数索引与图、范围计划；暂保留旧源码准备流程和兼容导入 |
| `stage3/` | 自然语言规约生成、审核、领域目录与输入材料准备 |
| `stage4/` | 需求提取、通用定义和引理候选、参考与验证义务结构、审核和交接校验 |
| `templates/` | 阶段一等结构契约；不要假定所有提示都在此目录 |
| `scripts/` | 图后端环境配置、安装与静态辅助脚本 |
| `.deps/`、`.venv-graph/` | 固定的外部图分析代码和依赖环境；不要直接修改上游绕过版本检查 |
| `tests/` | 机制、协议、预算、证据、交接和兼容性测试 |
| `runs/` | 运行配置、输入快照、任务、报告、失败和实验记录；不是默认模型可浏览的答案库 |
| `exports/`、`archives/`、`updates/` | 特定交付或历史整理材料；是否适用需查具体记录 |
| `TOOL_OPTIMIZATION.md` | 优化依据，包含尚未实现的目标，不作为完成清单 |
| `MATERIAL_DELIVERY.md` | 当前材料准备和读取协议 |
| `DEVELOPMENT.md` | 本文：整体架构、实现边界、改动入口与维护规则 |

### 2.3 代码结构图

```mermaid
flowchart LR
    CLI1["stage1.multi"] --> F["stage1.focused"]
    CLI2["stage2.__main__：仅静态准备"] -->|复用 prepare_only 分支| R["stage3.reference"]
    CLIN["stage3.__main__：自然规约"] --> R
    CLI3["stage4.__main__"] --> P3["stage4.pipeline"]
    SEL["stage2.select：函数组选择"] --> TASK
    SEL --> ST["selection_tools：静态依赖与材料评估"]
    ST --> SCOPE
    ST --> PREP

    F --> FC["focused_contracts<br/>模块与比较校验"]
    F --> TASK["stage1.task<br/>有预算的模型任务会话"]
    R --> INV["inventory / fm_graph<br/>函数标识与候选图"]
    R --> SCOPE["demand_scope / graph<br/>范围、SCC、调度"]
    R --> SCEN["scenario_guidance<br/>DOMAIN_CONCERNS.json"]
    R --> RR["reference_review<br/>独立审核与有限修订"]
    R --> READMODEL["read_materials.ReadingModel<br/>默认阶段三补读会话"]
    RR --> READMODEL
    R --> PREP["read_materials.SourcePreparation<br/>静态类型与宏候选"]
    P3 --> MAT["stage4.materials<br/>当前任务的输入数据与必读清单"]
    MAT --> PREP
    P3 --> CT["stage4.contracts / planning<br/>结构、证据、覆盖与状态"]
    P3 --> TASK
    TASK --> RD["Reader 或 BundleReader"]
    READMODEL --> RD
    FACTORY["stage1.model_factory<br/>ModelConfig / create_model"] --> BACK["现有 Codex / 显式 API 适配器"]
    TASK --> BACK
    READMODEL --> BACK
    RD --> INPUT["input 或已核验源码包"]
    TASK --> LOG["runs 中的运行配置、会话、状态与检查点"]
    READMODEL --> LOG
```

**两种执行路径不能混为一谈：**

- 阶段一、阶段二的函数组选择、阶段四和若干旧流程使用 `stage1.task.run_task`。
- 当前默认阶段三在 `reference.py` 中组织批次、格式修复与审核；`ReadingModel` 包装可选补读。它不是自动套用阶段四的 24 次角色调用预算。
- 所以修改公共执行器后，要确认当前默认入口是否真的调用它；只修改旧流程或帮助函数，不代表默认流程已经接入。

## 3. 阶段一：模块划分、比较与目标模块选择

本阶段的具体输入、输出及文件位置见 [输入输出说明](#阶段一模块划分比较与选择)。

源码依据：[focused.py](stage1/focused.py)、[focused_contracts.py](stage1/focused_contracts.py)。

```mermaid
flowchart TD
    A["模型：分别生成待证明库与各参考库的模块摘要<br/>及带依据的依赖规划"] --> B["静态：校验覆盖、端点、引用<br/>计算依赖候选与阻断"]
    B --> C["模型：推荐下一目标模块"]
    C --> D{"能否提出有依据的选择"}
    D -->|不能| X["needs_revision / incomplete<br/>保存原因"]
    D -->|能| E["模型：仅比较模块职责和范围摘要<br/>match / no_match / unknown"]
    E --> F["模型：深读目标和 match 参考模块<br/>模块任务可有限并发"]
    F --> G{"目标依赖复核是否确认"}
    G -->|否| X
    G -->|是| H["模型：按目标与参考逐对比较"]
    H --> I["模型：逐对独立审核<br/>没有 match 也审核目标范围"]
    I --> J{"独立审核全部通过<br/>输入快照未变化"}
    J -->|否| X
    J -->|是| K["final/report.json<br/>pending_user_review"]
    K -.-> U["人工决定下一阶段模块范围"]
```

初筛任务只能读取模块摘要，不能直接绕过初筛把全库源码装进上下文。源码深读与成对比较有各自上下文。未知依赖不能被当作已解决；模块图不是完整函数调用图。

阶段一默认入口并不保证任意中断状态都能自动恢复。`continue_saved.py` 和 `run_task(resume_from=...)` 提供受控续接机制，必须核对它们各自适用条件，不能据历史专用续接脚本宣称普遍支持自动恢复。

## 4. 阶段二：函数依赖图与待处理函数选择

本阶段的具体输入、输出及文件位置见 [输入输出说明](#阶段二函数依赖图与待处理函数选择)。

### 4.1 构建函数图

源码依据：[fm_graph.py](stage2/fm_graph.py)、[fm_graph_worker.py](stage2/fm_graph_worker.py)、[inventory.py](stage2/inventory.py)。

```mermaid
flowchart TD
    M["manifest：源文件范围、配置说明<br/>材料和输入版本"] --> I["静态：枚举函数定义与源码缺口"]
    I --> E["检查固定的 FM-Agent / CodeGraph 环境"]
    E --> C["建立分析源码副本<br/>使用或准备编译数据库"]
    C --> CG["CodeGraph：函数索引及候选关系"]
    C --> CL["Clang CLI：JSON AST"]
    CL --> DE["上游分析：直接调用边"]
    CG --> FB["未被成功 AST 覆盖的函数<br/>回退到索引候选"]
    CL --> FP["上游 C 间接调用分析<br/>值流与类型等候选"]
    CG --> FP
    DE --> MERGE["映射回当前精确函数 ID<br/>保留调用点、配置与证据"]
    FB --> MERGE
    FP --> MERGE
    I --> MERGE
    MERGE --> G["graph.json<br/>unverified_reference_graph"]
    MERGE --> U["unknown_calls / inventory_gaps<br/>解析与配置诊断"]
```

使用命令行 Clang AST，不是 Python libclang。CodeGraph 与 FM-Agent 均来自固定上游版本，具体版本与安装见 [FM_AGENT_GRAPH.md](stage2/FM_AGENT_GRAPH.md)。静态分析配置不是正式 QCP 证明配置。

函数 ID 区分源码位置及条件实现。函数指针目标和条件实现可能仍只是候选；AST 未覆盖、未映射的调用、宏和非 C 实现缺口必须保留。已有图的缺边不会被范围规划自动修复。本轮试验曾由监督侧补过候选边，这属于试验干预，不是图构建器已具备的能力。

`--prepare-only` 不调用规约模型，但在没有 `--scope-plan` 时可能实际构建函数图、运行静态分析工具；不能理解为完全不执行外部工具。

### 4.2 函数组选择

stage2/select.py 使用单个模型会话读取原文；selection_tools.py 提供底层候选、调用者、依赖增量、材料量与上限查询。超限和源码缺失由程序检查，未知调用和材料完整性仍保留为未知。输出 selection.json、assessment.json 及待用户确认的范围计划，不执行规约生成。详见 [函数组选择](stage2/SELECTION.md)。

选择器的输入是已保存的函数图、原始源码、用户指定的 README 等背景路径，以及批次和会话预算。模型只负责判断本批函数的用途及是否值得继续向上扩展；不先编写函数特性报告，不自行计算依赖数量。

| 静态查询 | 内容 |
| --- | --- |
| candidate_frontier | 按强连通分量提供底层候选及源码位置，保留未知调用 |
| direct_callers | 查询补齐依赖后函数组的直接调用者 |
| evaluate_group | 计算完整目标组、需求调用者、相对上一组的新增依赖、已定位材料大小和超限项 |
| scope_details | 分页读取成员、缺失源码、未解析调用及其他未知项 |

默认批次上限为 12 个目标函数、40 个生成范围函数、120000 个已知材料 JSON 字符；选择会话默认最多 16 次调用、900 秒、60000 字符上下文。两类预算不混用：前者用于控制批次工作量，后者约束当前模型会话。已知材料不包括未来生成的规约及尚未读取的参考内容，不能据此保证下一阶段的总 token 或证明耗时。

当前自动选择使用全部已识别上层调用需求，不自行裁剪需求入口或排除被调用依赖。若需要明确的范围边界，仍使用 demand_scope 人工请求路径。推荐规约不算已证明契约，不能据此自动扣除未处理依赖。结果必须经用户确认后进入阶段三。

### 4.3 version=2 范围规划

源码依据：[demand_scope.py](stage2/demand_scope.py)。输入是已有图和明确的函数 ID，不由该模块自动推荐一批目标。

角色定义：

| 角色 | 是否生成自然规约 | 是否进入阶段四 |
| --- | --- | --- |
| 用户指定目标 | 是 | 是 |
| 自动补入的被调用函数、同一递归分量成员 | 是，仍属 `target` | 是 |
| 向上传递需求的 `demand` 函数 | 是；当前仍生成完整规约 | 否，只提供背景 |
| `context` 边界函数 | 否 | 否，只提供背景与未解决条件 |

```mermaid
flowchart TD
    G["已保存图及运行配置校验"] --> T["人工指定或 agent 推荐的 target_ids"]
    T --> SCC["静态：完整候选图上的 SCC"]
    SCC --> DOWN["从原目标向下递归展开被调用依赖<br/>递归分量整体处理，共享节点去重"]
    B["可选 dependency_boundaries<br/>精确 ID 与排除原因"] --> DOWN
    DOWN --> TARGET["target_ids：完整处理组<br/>记录 requested / SCC / dependency 来源"]
    TARGET --> UP["向上追溯扩展后目标的调用需求"]
    ROOT["可选 root_ids"] --> UP
    UP --> MODE{"是否指定需求入口"}
    MODE -->|否| ALL["所有已识别祖先的并集"]
    MODE -->|是| PATH["保留入口到扩展后目标的全部路径<br/>原目标必须被入口覆盖"]
    ALL --> KEEP["generation_ids = target + demand"]
    PATH --> KEEP
    KEEP --> BOUND["保留范围外入边、辅助出边<br/>明确停止展开的被调用函数与未知项"]
    KEEP --> ORD["生成：caller-first<br/>建议证明顺序：callee-first SCC"]
    BOUND --> PLAN["scope-plan.json / SCOPE.md<br/>摘要绑定图、输入与 manifest"]
    ORD --> PLAN
    PLAN --> APPROVE["人工确认 plan_digest<br/>后续执行使用 approve-scope"]
```

关键规则：

- 旧草稿、同名函数或模型 `review=pass` 不作为“已验证契约”自动截断依赖；当前没有自动核验契约适用性的机制。
- 明确停止展开的被调用函数按 SCC 截断，必须可达且说明理由；不能排除原目标所在分量。依赖状态仍为未解决。
- 仅 `target_ids` 向下闭合。`demand` 函数的无关辅助调用保留为边界，不无限扩展整库。
- 入口截断不表示其他调用者没有需求；它们留在边界记录中。
- SCC 内没有严格的先后关系。建议证明顺序只表示图上依赖关系，不授权执行证明。
- version=1 历史计划仍按旧的祖先路径语义校验；启用新版行为应重新规划并确认摘要。

## 5. 阶段三：自顶向下生成自然语言规约

本阶段的具体输入、输出及文件位置见 [输入输出说明](#阶段三自顶向下生成自然语言规约)。

源码依据：[reference.py](stage3/reference.py)、[reference_review.py](stage3/reference_review.py)、[scenario_guidance.py](stage3/scenario_guidance.py)。

```mermaid
flowchart TD
    P["审核过的范围或完整 manifest"] --> S["静态：按 caller-first 排列 SCC<br/>过大分量按预算拆批"]
    S --> A["静态：组织完整实现、相邻需求<br/>领域目录、类型与宏候选原文"]
    A --> CHECK{"上层需求就绪<br/>输入能放入预算"}
    CHECK -->|否| BLOCK["upstream_incomplete / context_too_large<br/>保留批次状态"]
    CHECK -->|是| W["模型：同一次响应先分析情景<br/>再书写自然规约与 callee_requirements"]
    W --> READ{"是否缺少关键原文"}
    READ -->|是| RD["只读补读，可批量<br/>保持原上下文与时间预算"]
    RD --> W
    READ -->|否| V["静态：JSON、目标覆盖、领域 ID<br/>边和调用点绑定校验"]
    V -->|格式错误| FIX["最多一次格式修复"]
    FIX --> V
    V -->|通过| SAVE["保存 pending_review 草稿"]
    SAVE --> REVIEW["新会话：独立语义审核"]
    REVIEW --> VERDICT{"审核结论"}
    VERDICT -->|pass| COMMIT["保存 reference_draft 与审核摘要<br/>向下传递调用需求"]
    VERDICT -->|needs_revision 且有额度| REV["模型修订完整草稿"]
    REV --> REVIEW
    VERDICT -->|insufficient 或额度耗尽| STOP["保存最新草稿与原因<br/>阻止依赖它的后续任务"]
    COMMIT --> NEXT{"本次 generation_ids 全部完成"}
    NEXT -->|否| S
    NEXT -->|是| DONE["reviewed_reference_drafts<br/>semantic_review=true, proved=false"]
```

生成前情景分析在同一次生成响应内完成，**不是额外模型阶段**。`DOMAIN_CONCERNS.json` 同时维护通用要求、领域目录和关注点，程序检查结构与引用，不能据此判定分析语义正确。

规约采用职责与符号说明，以及命名规约的 `With / Require / Ensure`：

- 内存资源与数值条件共同写入前后条件，不另设独立 Memory/Modifies 分类。
- 入口快照必须绑定实际参数或资源；写入后不能把旧输入内容当成当前内存。
- 输出应可明确计算，或通过唯一结果关系与相应计算接口/等价义务连接。
- 允许 exists、析取、原地与分离契约；不能因为难证明就加强前提或缩小输入范围。
- 零长处理、资源自动匹配、C 指针和逻辑整数地址的缩放差异，仍须后续实际检查。

独立审核检查输入取值范围、精确输出、入口快照、内存资源、分支覆盖、调用需求、假设、计算接口。`insufficient` 不进入盲目语义重试；默认最多一次语义修订。格式修复与语义修订是不同额度。

显式 `--skip-review` 仍可生成未审核稿，但状态不能伪装为已审核。本节主图描述默认审核开启的路径。

## 6. 任务输入准备、读取和来源记录

源码依据：[read_materials.py](stage3/read_materials.py)、[materials.py](stage4/materials.py)、[reader.py](stage1/reader.py)、[task.py](stage1/task.py)。完整协议见 [MATERIAL_DELIVERY.md](MATERIAL_DELIVERY.md)。

### 6.1 当前静态准备的职责

- `SourcePreparation` 有界遍历本地 include，按词法标识符定位类型和宏候选，递归补充候选依赖，并保留宏续行及外层条件历史。
- 条件分支不求值，缺少系统/生成头文件、非字面 include、解析失败或遍历上限均保留为缺口。
- 同文件的路径和哈希分组保存；重复的缺失 include 保留全部来源后合并表示。
- 阶段四按任务筛选背景，完整相关条件仍保留，未直接放入模型输入的记录保存为可按需读取的索引。
- inventory 缺口无法可靠归属单函数，必读视图保留其全局未知影响。未展开不是已经证明无关。
- 同一会话的必读源码区间先合并去重，再分段交付。跨角色可以复用定位结果，**不能据此声称另一个模型任务已阅读或审核同一材料**。

### 6.2 任务输入准备与读取流程图

```mermaid
flowchart TD
    JOB["当前角色与目标 IDs"] --> VIEW["静态：构造相关规约、调用需求<br/>条件与未知项视图"]
    JOB --> SRC["静态：已知源码坐标<br/>类型、宏和引用原文定位"]
    VIEW --> IDX["其他背景保留索引<br/>完整原件仍可读取"]
    VIEW --> LIST["生成角色必读材料清单"]
    SRC --> LIST
    LIST --> D{"Reader 能完整交付<br/>且保留输出预算"}
    D -->|否| GAP["模型调用前停止<br/>needs_material / 材料缺口"]
    D -->|是| INPUT["当前角色获得原文与派生材料<br/>分别标记来源和信任状态"]
    INPUT --> MODEL["模型作语义分析"]
    IDX -->|按需查阅| MODEL
    MODEL --> NEED{"还需补充材料"}
    NEED -->|否| OUTPUT["提交候选或审核结果"]
    NEED -->|是| ACTION["read / search / list<br/>或 batch 独立动作"]
    ACTION --> SAFETY["静态：路径、角色权限、源码包边界<br/>批量大小与剩余预算"]
    SAFETY -->|可交付| RESULT["交付结果并记录实际阅读"]
    RESULT --> MODEL
    SAFETY -->|超限或不可用| KEEP["保存诊断；未交付原文<br/>不能作为已读取的源码依据"]
    KEEP --> MODEL
```

这张图主要表示 `run_task` 的阶段四必读交付路径。默认阶段三把准备好的实现和辅助原文直接放入 assignment，超限由批次预检处理；补读由 `ReadingModel` 实现。两者使用相同的原始输入边界，但状态文件布局不完全相同。

### 6.3 检索、批量读取和保存

- search 支持单文件与目录。默认 20 个命中、最多 40 个，片段最多 160 字符；连续检索使用完整 `next_action`，不能只沿用文件 offset 而漏掉同文件后续命中。
- batch 一次 1–8 个独立 read/search/list，不允许嵌套。依赖前一步结果的请求仍分开进行。
- 批次结果超过 24000 字符时整体不交付，并撤回本批新增引用依据；任务级预算还有独立检查。
- 搜索片段、源码索引、旧提取报告和模型自述都不是当前模型任务实际读取的原文。`reads.jsonl` 中存在执行记录也不必然代表交付成功，需结合会话与 withheld 记录判断。
- 默认源码包兼容输入只能用 `BundleReader` 读包内原文，不回退到完整库。
- `run_task` 的固定理解草稿频率目前仍保留；本轮材料优化没有取消它。不要把建议中的“纯程序自动检查点替代所有草稿轮次”写成已实现。

## 7. 阶段四：生成通用定义和引理

本阶段的具体输入、输出及文件位置见 [输入输出说明](#阶段四生成通用定义和引理)。

源码依据：[pipeline.py](stage4/pipeline.py)、[contracts.py](stage4/contracts.py)、[planning.py](stage4/planning.py)、[prompts.py](stage4/prompts.py)。

阶段四首先核对阶段三的运行配置、输入快照、本批全部函数的完成状态、审核策略、规约/源码摘要及范围批准。读取旧未审核输入有显式兼容路径，但不会改写上游审核与证明状态。

```mermaid
flowchart TD
    S2["阶段三输出目录"] --> GATE["静态：校验完整 generation_ids<br/>运行配置、快照、范围与审核状态"]
    GATE -->|不一致| REJECT["拒绝交接；不启动生成"]
    GATE -->|一致| TARGET["只选择完整 target_ids<br/>包含向下补入的依赖"]
    TARGET --> EXT["模型：每函数独立提取 needs<br/>条款、使用点、共享或局部用途"]
    EXT --> EV["静态：格式、原文证据与目标覆盖"]
    EV -->|通过| SAVE["functions/id/common_needs.json"]
    EV -->|未完成| STOP["incomplete，保留已有提取"]
    SAVE --> ALL{"全部目标提取完成"}
    ALL -->|否| EXT
    ALL -->|是| COMMON["模型：整组通用定义与引理设计<br/>按需比较原始参考方案"]
    COMMON --> TRACE["references：定义、性质、边界<br/>实际使用、环境"]
    TRACE --> DECIDE["coverage：reuse / adapt / supplement<br/>new / not_needed / unknown"]
    DECIDE --> ITEMS["items：参数、前提、陈述、用途<br/>依赖与 validation_obligations"]
    ITEMS --> VALIDATE["静态：逐项覆盖、引用、依赖无环<br/>上游条件和义务状态"]
    VALIDATE -->|通过| CAND["candidate.json / candidate.md<br/>planning.json：execution_status=not_started"]
    VALIDATE -->|未通过且无法完成| STOP
    CAND --> REVIEW["独立模型审核：重新获得相关原文<br/>检查适用性、强度、边界与覆盖"]
    REVIEW --> VERDICT{"审核结论"}
    VERDICT -->|needs_revision 且有额度| COMMON
    VERDICT -->|pass| DONE["common_candidates_reviewed<br/>仍为 not_proved"]
    VERDICT -->|其他或额度耗尽| LIMITED["保留候选、review 和未决项"]
```

当前仍是**逐函数提取，再汇总本批函数需求**。尚未改为小组联合提取，不具备自动判定数学表示等价或跨运行公共库复用的能力。

参考记录的五个方面是需要回答的问题，不强制每个数学定义都附带指针别名案例。资源谓词应追溯其定义、相关边界引理与实际用法。未找到、不适用、尚未知必须分开；不能把参考库成立当成当前配置已实测。

每项验证义务写清目的、方法、环境、成功标准，只允许 `planned / blocked / not_applicable`。正常待执行义务不是已经证明，也不能用一项遥远的验证计划掩盖当前候选的核心语义缺口。

### 参考 strategy 的交接

选定参考定义或引理后，附上直接相关 strategy 的原文和正确性证明位置；不加入 C 使用示例。模型提供来源坐标，程序按当前读取权限提取，不让模型重写规则。候选项目用 strategy_ids 关联附件。

阶段四新增 reference_strategies/index.json 和按内容哈希命名的 .strategies 文件。索引包含原始路径、行号、哈希、参考及候选 ID、证明位置、依赖和适用性。candidate.json 保存关联，planning.json 保存来源记录，candidate.md 显示规则 ID。没有适用附件时仍输出空索引。

这些规则均为目标适用性未验证、未安装。后续 QCP agent 判断是否采用；缺少证明时保留未知。修订以最新索引为准，恢复时核对候选和文件哈希。详见 [阶段四附件协议](stage4/COMMON_CONTENT_TEMPLATE.md)。

## 8. 产物、状态与恢复

### 8.1 各阶段的输入与输出

以下先描述数据的具体内容，再给出文件位置和用途。路径相对于对应步骤的输出目录；`<id>` 是函数或模块的唯一标识。“主要输出”是下一阶段需要的数据；运行配置、日志和检查点另列为辅助文件。失败或中断时不保证所有输出均已产生。

#### 阶段一：模块划分、比较与选择

**输入**

| 具体内容 | 读取位置 | 用途 |
| --- | --- | --- |
| 待证明库的函数实现、头文件、目录结构和可用说明 | `input/` 内的目标库目录 | 划分模块，分析职责和依赖 |
| 各已证明参考库的实现、规约、Coq 定义、引理、证明及说明 | `input/` 内的参考库目录 | 先比较模块职责，再阅读可能适用的参考内容 |
| 模块数量限制、模型配置、时间和上下文预算 | 命令参数 | 控制执行资源 |

**主要输出**

| 具体内容 | 保存位置 | 用途 |
| --- | --- | --- |
| 各库模块的标识、职责、源文件范围、依赖和源码依据 | `plan.json / .md` | 描述模块划分 |
| 模块间依赖关系、可推荐模块和阻碍处理的依赖 | `dependency_graph.json / .md`、`dependency_frontier.json / .md` | 支持选择当前目标模块 |
| 推荐目标模块及选择理由 | `selection.json / .md` | 提交用户决定 |
| 每个参考模块与目标模块的匹配结论及理由：适用、不适用或未知 | `screening.json / .md` | 决定详细阅读哪些参考模块 |
| 模块实现分析、依赖复核；每对模块的相似点、差异和可复用内容 | `modules/<id>.json / .md`、`comparisons/<参考模块ID>.json / .md` | 为后续函数分析提供背景 |
| 审核问题、结论、选定模块和未确定的参考关系 | `reviews/`、`final/report.json / .md` | 用户确认本轮模块选择 |

**传给阶段二：** 用户确认的目标模块与参考模块、目标源文件范围、模块说明引用、源码版本和配置说明。当前需整理为 manifest；`final/report.json` 不能直接替代 manifest。

#### 阶段二：函数依赖图与待处理函数选择

**输入**

| 具体内容 | 读取位置 | 用途 |
| --- | --- | --- |
| 选定模块的源文件范围、目标/参考模块说明引用、源码版本和配置说明 | manifest 及引用材料 | 确定分析对象 |
| C 实现、头文件、宏和可用编译命令 | 原始输入及图分析工作目录 | 枚举具体函数定义，分析调用关系 |
| 人工选择时：初始目标函数 ID，可选的上层调用入口，以及不继续展开的函数及原因 | request JSON 的 `target_ids`、`root_ids`、`dependency_boundaries` | 作为 demand_scope 的人工请求 |
| 自动选择时：背景原文的相对路径、目标数/生成范围数/已知材料量上限、当前选择会话预算 | select 的 --background、--max-*、--calls、--seconds、--context-chars | 让模型直接阅读原文，由程序计算依赖和预算；不要求预先指定目标 ID |

**主要输出**

| 具体内容 | 保存位置 | 用途 |
| --- | --- | --- |
| 函数 ID、名称、源码位置、配置或实现变体信息 | 图运行的 `graph.json` 节点及相关记录 | 唯一区分函数实现 |
| 调用者、被调用者、调用点和分析依据；无法确定目标的调用、解析失败和枚举缺口 | 同一 `graph.json` 的边、未知调用和诊断记录 | 建立函数依赖图，保留不确定性 |
| 原始请求函数，以及补入被调用依赖和递归分量后的完整目标函数组 | `scope-plan.json` 的 `requested_target_ids`、`target_ids` 等字段 | 明确本批处理对象 |
| 用于推导需求的上层调用者、仅作背景的范围外函数、跨范围调用边和明确排除的依赖 | `scope-plan.json` 及范围目录的 `graph.json` | 确定哪些调用需求需要分析、哪些依赖暂不处理 |
| 规约生成顺序、建议证明顺序、强连通分量、未知项和计划摘要 | `scope-plan.json`；可读版本 `SCOPE.md` | 安排处理顺序，供用户确认 |

自动选择还产生以下内容：

| 具体内容 | 保存位置 | 用途 |
| --- | --- | --- |
| 初始目标 ID、功能价值理由、停止扩展的原因、实际阅读的源码引用及评估标识 | selection.json | 让用户核对选择依据 |
| 完整依赖范围、数量、已定位材料大小、配置上限及缺失/未知记录 | assessment.json | 核对静态计算结果 |
| 选择任务来源、配置、工具调用和模型会话记录 | identity.json、task/、status.json | 排错与复现；不代表已完成人工确认 |

**传给阶段三：** 用户确认的函数组、相关调用者与边界、调用图及源码位置、规约生成顺序，以及阶段一模块说明。`plan_digest` 是计划内容摘要，不是正确性证明。

图运行与范围运行各有一个 `graph.json`：前者是模块分析图，后者是按本轮范围选取的图。二者均不表示自然语言规约已经生成完成。

#### 阶段三：自顶向下生成自然语言规约

**输入**

| 具体内容 | 读取位置 | 用途 |
| --- | --- | --- |
| 本批函数、需求调用者、范围边界、调用点和生成顺序 | 已确认的范围计划、函数图及 manifest | 确定生成对象和调用需求传播关系 |
| 当前函数完整实现、相关类型、宏、条件编译分支和必要调用点原文 | 原始源码及静态定位、按需读取结果 | 分析实际行为及适用配置 |
| 模块职责，以及已有调用者对当前函数的参数条件、结果要求和调用场景 | 模块说明、图中调用边的需求记录 | 汇总多个调用点需求 |
| 通用写作要求、领域关注点，以及需要时补读的参考材料 | 本轮 `writing-guidance.json`、允许读取的原文 | 先分析情景，再写规约；不默认所有参考材料已经读过 |

**主要输出**

| 具体内容 | 保存位置 | 用途 |
| --- | --- | --- |
| 适用领域、函数行为概括、边界条件、关注事项及分析依据 | `specs/<函数ID>.json` 的 `scenario_analysis`；对应 Markdown | 说明生成者如何理解函数 |
| 逻辑参数及符号含义、入口旧值、前置条件、精确后置条件、边界情况；内存资源和修改结果写在前后条件中 | `specs/<函数ID>.json / .md`，并存入生成运行的 `graph.json` 节点 | 交付自然语言推荐规约 |
| 对各被调用函数的参数条件、结果要求及调用点依据 | 规约中的 `callee_requirements`，经校验后关联到 `graph.json` 调用边 | 为被调用函数生成规约提供需求 |
| 未解析行为、缺少材料、适用配置、额外假设及尚未确认事项 | 规约和相关图记录 | 明确推荐规约的适用范围和不确定性 |
| 审核意见、修改要求、修订后的规约及逐函数审核结果 | 批次任务审核/修订记录、`graph.json`、`status.json` | 决定是否进入阶段四，不代表形式化证明通过 |

**传给阶段四：** 完整生成运行目录中的最终规约、逐调用点需求、假设与未知项、审核结论、函数范围及输入版本。阶段四用 `--stage3-run` 读取这个目录；这是当前参数名；旧参数 --stage2-run 仍可作为兼容别名。

默认需要整个生成范围完成审核，包括上层需求调用者。阶段四仅为 `target_ids` 提取公共需求，上层调用者规约仍是背景。显式跳过审核时必须保留“未审核”状态。

#### 阶段四：生成通用定义和引理

**输入**

| 具体内容 | 读取位置 | 用途 |
| --- | --- | --- |
| 本批目标函数的自然语言规约、输入条件、结果要求和未决问题 | 阶段三运行目录 | 确定所需数学表示、计算定义和正确性性质 |
| 函数实现、调用需求、内存资源和配置条件 | 函数图及原始源码 | 确定连接 C 运算、内存断言和数学模型的定义与引理 |
| 参考库定义、相关谓词、正确性和边界引理、实际调用者、导入及使用约束 | 各已证明参考库的原始材料，按任务读取 | 比较方案，判断复用、适配或新建 |
| 上游审核结论及来源记录 | 阶段三状态及审核记录 | 区分已审核推荐规约和已证明契约 |

**当前主要输出**

| 具体内容 | 保存位置 | 用途 |
| --- | --- | --- |
| 每函数缺少的定义或性质、对应规约条款、预计使用位置及共享/局部用途 | `functions/<函数ID>/common_needs.json` | 汇总本批函数需求 |
| 参考定义和引理的来源、已阅读内容，以及未找到、不适用或未知的部分 | `candidate.json` 的 `references`；`planning.json` 对应记录 | 说明设计依据与未解决问题 |
| 每项需求选择直接复用、适配、补充、新建、无需通用定义或引理或未知的决定及理由 | `candidate.json` 的 `coverage`；`planning.json` 的 `decisions` | 解释需求如何得到满足 |
| 候选定义或引理的名称、参数、前提、陈述、用途、相互依赖及需求对应关系 | `candidate.json` 的 `items`；`candidate.md` | 作为后续 Coq 实现的设计输入，尚不是可编译源码 |
| 每个候选项目需要完成的编译检查、证明或 QCP 使用检查，以及当前计划状态 | 各 item 的 `validation_obligations`；`planning.json` | 安排后续验证，不表示已经通过 |
| 设计的审核问题、结论和完成情况 | `review.json`、`status.json`、`SUMMARY.md` | 决定是否继续修改设计 |

**计划中的最终输出，尚未自动实现：** 包含实际 Coq 定义、引理陈述和证明脚本的 `.v` 文件，编译与证明结果，以及当前 QCP 环境的导入和使用检查结果。这些才是后续形式化函数规约和证明所需的公共库及验证记录。

当前审核通过仅得到 `common_candidates_reviewed`；`planning.json` 仍为 `proof_status=not_proved`、`execution_status=not_started`。

#### 独立源码准备：不是上述阶段的必经步骤

| 类型 | 具体内容 | 文件位置 |
| --- | --- | --- |
| 输入 | 函数实现、必要类型和宏、callee 声明、可选的匹配契约 | 原始输入、manifest 和显式传入的契约 |
| 提取输出 | 每函数一个 C 文件，包含实现、声明和可用规约；另记录来源位置、覆盖范围、缺失内容及人工修改 | `<函数ID>.c`、`preparation.json`、`REVIEW.md` |
| 人工审核后输出 | 修改并确认的 C 文件、文件哈希、源码映射、配置和审核记录 | `<函数ID>.c`、`prepared.json` |

`stage2.prepare approve` 只保存已填写的审核记录，不代替人工审核、编译或等价性证明。

#### 辅助文件：版本、状态和运行记录

| 具体内容 | 文件位置 | 用途 |
| --- | --- | --- |
| 输入文件版本、模型参数、提示与策略版本、内容摘要 | `input_snapshot.json`、`identity.json`（按入口保存） | 防止混用不同配置或源码版本的结果 |
| 本轮写作要求 | `writing-guidance.json` | 保证生成与修订采用相同规则 |
| 上游来源、审核情况、函数范围和适用条件 | 阶段四的 `upstream_context.json`、`upstream_conditions.json` | 保留上游结果的条件与验证状态 |
| 模型实际收到的输入、响应、源码读取记录和失败原因 | `tasks/`、`material-sessions/` 等任务目录 | 重现判断依据；不同执行器的日志布局不同 |
| 必须提供的原文清单、缺少的材料、因预算不足而未发送的内容 | `required_inputs.json`、`material_gap.json`、`withheld-feedback-*` | 解释材料不足；未发送原文不能计为已阅读 |
| 已完成任务、当前结果和中断位置 | `status.json`、`checkpoint.json` 或 `checkpoints/` | 控制恢复；文件存在不等于执行成功 |

`run_task` 的 `report.json` 表示通过对应角色的输出校验，不自动表示语义正确。当前范围协议与通用定义规划协议均为 version=2，材料准备策略为 version=1；具体版本以代码和运行记录为准。

### 各阶段的数据传递

```mermaid
flowchart LR
    A["阶段一输出<br/>模块职责、文件范围、依赖和参考适用性"] --> B["阶段二输入<br/>确认后的模块信息与源码"]
    B --> C["阶段二输出<br/>调用图、本批函数、需求调用者、边界和顺序"]
    C --> D["阶段三输入<br/>函数范围、实现、调用需求和写作要求"]
    D --> E["阶段三输出<br/>逻辑参数、前后条件、callee 需求、假设、未知项和审核意见"]
    E --> F["阶段四输入<br/>本批规约、实现、参考定义与引理"]
    F --> G["当前输出<br/>需求、候选陈述、复用选择、参考依据、验证义务和审核意见"]
    G -.-> H["待实现输出<br/>Coq 定义和引理文件、编译证明结果、QCP 使用检查结果"]
```

### 8.2 状态不能混读

| 状态或标记 | 意义 |
| --- | --- |
| `task_completed` | 某个角色输出通过对应结构/证据校验，不自动等于语义审核通过 |
| `pending_user_review` | 模块或函数组结果等待人工确认；选择器不会自动启动阶段三 |
| `selection_unavailable` | 本次选择会话未提出合适批次；不代表整个模块不存在可处理函数组 |
| `reference_draft` | 单函数参考稿；是否审核需核对其审核报告与总体策略 |
| `reviewed_reference_drafts` | 默认阶段三本批全部函数的模型审核通过；`proved=false` |
| `drafts_generated` | 显式未审核流程的本批全部函数生成完成 |
| `common_candidates_reviewed` | 通用定义和引理候选模型审核通过，可继续形式化；不是编译或证明通过 |
| `needs_material` | 当前必需材料不可得或无法在预算内交付 |
| `review_insufficient` / `review_needs_revision` | 自然规约材料不足或语义修订未完成 |
| `incomplete` / `interrupted` / `failed` | 工作未完成；查看具体任务 reason，不概括成 OOM |
| `not_proved` / `not_started` | 分别表示未证明、验证执行尚未开始 |

### 8.3 恢复与返工边界

```mermaid
flowchart TD
    CHANGE["重新执行或请求 resume"] --> ID{"输入、模型、范围、提示<br/>材料准备与规划策略版本是否一致"}
    ID -->|否| NEW["拒绝原配置继续执行<br/>建立新计划或新输出目录"]
    ID -->|是| CHECK{"检查点与状态摘要一致"}
    CHECK -->|否| REJECT["拒绝恢复；定位配置或文件变化"]
    CHECK -->|是| STAGE{"所属执行路径"}
    STAGE -->|阶段三| R2["复用已通过结果<br/>未通过批次新建 attempt"]
    R2 --> PROP["调用者审核变化<br/>使图中可达的被调用函数审核结果失效"]
    STAGE -->|阶段四| R3["复用已完成函数提取<br/>继续缺失规划或审核"]
    STAGE -->|显式角色恢复| RT["run_task resume_from<br/>校验已交付原文哈希与 artifact"]
    R3 --> NOTE["不等于无损续接所有中断会话<br/>恢复流程进度与恢复单个模型会话是两种操作"]
    RT --> NOTE
```

阶段四停止任务可通过 --recover-from 在新目录修复并重新校验；这不等于跨计划复用或输入迁移。跨计划自动复用旧规约、精准语义失效分析、递归分量固定点协调尚未实现。不得手工把失败状态改成 pass 来恢复。

## 9. 后续形式化与反馈应落在哪一步

以下是开发方向与实验教训，不是当前默认自动链：

| 发现的问题 | 应返回的位置 | 不应采取的做法 |
| --- | --- | --- |
| 调用边遗漏、配置候选不全 | 函数图/范围规划 | 把未知当叶子 |
| 宏、类型、副作用或调用背景缺失 | 材料准备/需求分析 | 直接增加前置条件掩盖 |
| 输入取值范围被缩小、输出不精确 | 自然规约生成与审核 | 用函数体证明通过替代域合理性检查 |
| 数学表示或参考适配不合适 | 阶段四需求、参考和复用选择 | 预设特定证明算法强行套用 |
| C 指针与整数地址偏移单位混淆 | 形式化规约生成和 spec_check | 因“证明通过”而接受过强地址条件 |
| 零长/别名契约无法被调用 | 最小调用测试及规约表达 | 宣称 QCP 普遍不支持析取 |
| Coq 可编译但 QCP 不能使用 | 通用定义和引理环境与实际使用检查 | 将编译当作集成验收 |
| 证明失败或义务改变 | 对应规约、公共定义、实现适配步骤 | 弱化结论、无依据加强前提、修改封存验收 |

建议未来链路为：参考规约及调用者阅读 → 候选形式化规约 → 语义和边界检查 → 最小调用测试 → 固定规约 → 完整证明。规约变化后记录差异与受影响义务，复用不受影响内容仍需最终一致性检查。QCP 的 auto_proof 由 QCP 自身流程负责，不额外重复审查。

## 10. 操作入口：静态准备与真实模型运行分开

以下是命令模板，不代表本文整理过程中执行了这些模型任务。输出目录必须是新的；示例使用现有 BN manifest，其输入哈希和材料适用性仍应核对。

### 10.1 图准备与函数组选择

已有图可以直接跳过第一条：

```bash
python3 -m stage2 \
  --manifest stage2/manifests/openssl-bn-module.json \
  --output runs/new-bn-graph --prepare-only

python3 -m stage2.demand_scope \
  --input input --graph-run runs/new-bn-graph \
  --request path/to/request.json --output runs/new-bn-scope
```

`request.json` 示例：

```json
{
  "target_ids": ["从 graph.json 读取的确切函数ID"],
  "root_ids": ["从 graph.json 读取的需求入口ID"],
  "dependency_boundaries": []
}
```

省略 `root_ids` 表示追溯全部已识别祖先；不能用空数组表达没有需求。若只希望从目标自身开始，可明确将入口设为目标 IDs，其他调用者会记录为范围边界。不能用裸函数名代替 ID。

也可用自动选择替代手写 request 的步骤。**以下命令会调用模型**；background 应替换为 input 内实际的待证明库背景文件路径：

```bash
python3 -m stage2.select \
  --input input --graph-run runs/new-bn-graph \
  --background target-library/README.md \
  --output runs/new-bn-scope \
  --max-targets 12 --max-generation 40 --max-material-chars 120000 \
  --calls 16 --seconds 900 --context-chars 60000
```

两条选择路径只选其一，输出目录必须不存在。自动选择也生成同格式 scope-plan.json；检查 selection.json、assessment.json 和 SCOPE.md 后，再批准其 plan_digest。它不自动继续生成规约。

先检查材料和范围，不调用模型：

```bash
python3 -m stage3 \
  --manifest stage2/manifests/openssl-bn-module.json \
  --scope-plan runs/new-bn-scope/scope-plan.json \
  --output runs/new-bn-specs --prepare-only
```

### 10.2 确认范围后运行模型

```bash
python3 -m stage3 \
  --manifest stage2/manifests/openssl-bn-module.json \
  --scope-plan runs/new-bn-scope/scope-plan.json \
  --approve-scope PLAN_DIGEST_FROM_SCOPE_PLAN \
  --output runs/new-bn-specs --resume \
  --model gpt-6.1-sol --reasoning-effort high

python3 -m stage4 \
  --stage3-run runs/new-bn-specs \
  --output runs/new-bn-common \
  --model gpt-6.1-sol --reasoning-effort high
```

也可以给阶段三加 `--with-common --common-output runs/new-bn-common`。阶段三和阶段四预算不同，自动交接不把阶段三所有预算参数直接传入阶段四。

| 当前默认预算 | 阶段三 reference | 阶段四角色任务 |
| --- | --- | --- |
| 应用层上下文 | 60000 字符 | 60000 字符 |
| 单次调用超时 | 600 秒；补读共享本次 exchange 剩余时间 | 600 秒，且受任务剩余时间及预留限制 |
| 补读/调用额度 | 单个模型任务会话最多 8 轮补读后提交结果；格式/语义修复另有边界 | 每任务默认 24 次模型调用 |
| 总任务时间 | 不是阶段四式 1800 秒角色预算 | 默认 1800 秒 |
| 语义修订 | 默认 1 次 | 默认 1 次 |
| 报告限制 | 受上下文及输出预留约束 | 候选最多 24000 字符；仍受总预算约束 |

字符数不是计费 token。新增材料可能使必读预检超限；优先拆分任务或减少重复材料，不静默截断原文，不用无上限参数掩盖结构问题。

### 10.3 后端与环境

默认 CLI 使用 `stage1/codex_backend.py`，要求适用的 Linux/WSL、Codex CLI 登录及 bubblewrap 环境；环境以实际预检为准，历史“登录成功”不是当前可用性保证。图后端另有 `scripts/setup_graph.sh`、固定上游及依赖环境。

Windows Codex 原生子 agent 的试验适配器采用任务输入约束和 Reader，不等同于默认后端的操作系统隔离。不要混写两种隔离保证，不复制凭据，不因容量/认证错误反复重试，也不自行重启 WSL。

## 11. 修改代码时从哪里开始

| 修改内容 | 首要代码 | 应检查的联动 |
| --- | --- | --- |
| 函数图、调用点、条件实现 | `stage2/fm_graph.py`、`fm_graph_worker.py`、`inventory.py` | 精确 ID、未知记录、来源与版本、范围计划失效 |
| 上下游范围和边界 | `stage2/demand_scope.py` | project、caller-first、阶段四 target 覆盖、v1 兼容 |
| 情景分析、领域要求 | `stage3/scenario_guidance.py`、`DOMAIN_CONCERNS.json` | 目录摘要、修订输出、审核字段、旧运行恢复 |
| 自然规约与审核 | `reference.py`、`reference_review.py` | 模板、caller 要求、pass 门槛、被调用函数结果失效 |
| 静态类型/宏材料 | `read_materials.py`、`macro_units.py` | 条件历史、源坐标、预算、独立审核实际接收 |
| 当前任务的背景数据与必读清单 | `stage4/materials.py`、`stage2/required_inputs.py` | 两者所在流程不同；不能只改旧入口帮助函数 |
| Reader/批量/预算/恢复 | `stage1/reader.py`、`task.py`、`stage2/bundle_reader.py` | 未交付证据回滚、权限、源码包、会话恢复 |
| 阶段四字段与候选 | `stage4/prompts.py`、`contracts.py`、`planning.py` | 需求映射、假设继承、依赖循环、版本、义务状态 |
| 后端或原生会话适配 | `stage1/codex_backend.py`；明确选定的适配器 | 隔离、预算、运行配置、失败分类；不要直接提升实验脚本为默认 |

一次改动至少回答：

- 默认入口是否真正经过新代码？
- 新字段由谁产生、谁消费、谁校验、存在哪里？
- 是否改变源材料范围、输入取值范围、证明责任或实际引用依据？
- 新策略如何影响运行配置摘要和旧运行恢复？
- 回归测试证明的是机制还是语义？是否需要新的真实试运行？

## 12. 测试、实验和待办

### 测试入口

```bash
python3 -m unittest tests.test_function_selection tests.test_stage_layout tests.test_demand_scope
python3 -m unittest tests.test_material_delivery tests.test_required_inputs
python3 -m unittest tests.test_reference_specs tests.test_reference_review
python3 -m unittest tests.test_stage3 tests.test_reference_stage3 tests.test_stage3_planning
python3 -m unittest discover -s tests
```

2026-10-30 函数组选择功能回归记录为 377 项、374 项通过、3 项跳过。覆盖共享依赖去重、递归分量、未知调用、上层需求预算、材料缺失、范围计划加载和入口兼容。它是日期限定的开发记录，不是永久测试总数；新增测试后应更新记录。静态检查和测试替身通过不能代替真实模型结果、Coq 编译、QCP 调用或函数体证明。

本次材料优化的 `bn_sub_words` 静态预检：背景约 61330 → 19734 字符，21 项必读材料全部交付，首次请求约 45118 字符，可放入默认 60000 字符预算并保留输出空间。没有调用真实模型，不能据此声称已节省同等比例的 token 或总时间。

### 实验边界

- [既有 BN 实验报告](runs/isolated-bn-words-sol61-high-20261020-01/evaluation/FINAL_EXPERIMENT_REPORT.md)：10 个函数、12 个证明案例，只覆盖报告明确的配置、输入取值范围和别名条件，不代表整个 BN 模块完成证明。
- [本轮加减法试运行](runs/isolated-bn-add-sub-sol61-high-20261029-01/PILOT_REPORT.md)：阶段三 5 份参考稿与阶段四 3 份需求提取完成，通用定义与引理设计因模型容量问题未完成；未生成公共 Coq 文件，未执行 QCP。包含监督补图边和补原文等干预，不能称默认流程能够在无人干预下完成。
- 参考内容被使用不等于稳定节省总 token。准备、自然规约、通用定义与引理设计和证明成本应分开记录；服务等待与交接延迟也不能全部算作模型推理时间。
- 已确认的符号执行 OOM 与原因未定的 WSL 中断要分开记录，不能以同一原因概括。

### 尚未实现或尚未验证

1. 图构建器仍可能漏直接调用、条件实现或间接目标；范围展开不能弥补缺边。
2. 背景调用者仍生成完整规约，尚未改为仅分析调用需求。
3. 阶段四仍逐函数提取，再汇总本批函数需求；未实现小组联合提取和自动语义去重。
4. 参考库通用语义索引、自动充分性判定、跨运行公共库管理尚未实现。
5. 已验证 callee 契约的自动适用性匹配及据此截断依赖尚未实现。
6. 跨计划规约复用、精确增量失效和 SCC 固定点协调尚未实现。
7. 固定频率草稿、控制 agent 逐次交接等成本问题尚未全部解决。
8. Coq 生成执行、形式化规约及 spec_check、最小调用测试和正式证明交接仍需接入。
9. 本轮模型审核曾接受 `BN_uadd` 的输入范围收缩；不能将 pass 当作原域保持的保证。
10. 上述后续工作不能通过弱化结论、增加无依据前提或改验收文件来“跑通”。

## 13. 本文变更记录

| 日期 | 变化 | 验证方式 |
| --- | --- | --- |
| 2026-10-30 | 将旧开发说明归档，建立现行架构与流程文档；统一入口、阶段职责、任务输入准备与读取、状态、恢复和待办；增加详细流程图 | 对照默认入口、范围/材料/规划代码与已有运行记录；检查文档链接和命令参数 |

2026-10-30 补充：采用模块选择、函数图与函数组选择、自然语言规约、通用定义和引理四阶段划分；输入输出改为具体数据内容、文件位置、用途三列；增加术语解释。代码包已按四阶段迁移；历史文件未改名。

目录迁移兼容说明：旧 stage2.reference 等四个模块保留转发导入；原 python -m stage3 的公共候选命令改为 python -m stage4，新 stage3 不自动猜测旧命令意图。阶段二暂复用阶段三实现中的静态准备分支，避免改变已有图格式；后续可独立抽取准备服务。旧运行的字段、提示版本和状态语义未批量改写，恢复仍须通过原有配置与内容检查。

通用性说明更新：工具输入为一个待证明库和若干个已证明参考库；OpenSSL、SM2、mini-GMP 仅作为当前案例。文档区分通用设计与阶段一尚存的案例专用实现。

2026-10-30：新增阶段二单会话函数组选择；静态工具提供依赖增量、已知材料大小和上限检查。结果需人工确认；未执行真实模型选择实验。

2026-11-02：阶段四增加参考 strategy 原文附件、来源与证明索引、候选关联和恢复完整性检查。没有新增 C 使用示例、strategy 生成或自动安装步骤。

## 报告修复与重新校验（2026-11-02）

新增 --recover-from，在新目录复用停止任务的原报告、会话和已完成提取。先完整重新校验；仍有问题时，按错误补读或修订，再完整校验并继续独立审核。新增 --max-report-chars（正整数或 unlimited，默认 24000），提示与校验共用上限；不会自动放宽预算。格式错误保留原响应并有界修复。未接入输入修订及分项审查。

详细检查、命令和产物见 [报告恢复说明](stage4/RECOVERY.md)。共享执行器修改也影响阶段一、阶段二选择及其他调用方；完整回归不可省略。

## 分项审查与输入修订（2026-11-02）

--component-review 提供逐候选反馈和 retain/revise/add_material 动作。partial 仅表示部分设计通过审核，不能作为整体成功。--input-transition 与 --revise-from 在新目录记录精确新增文件清单，禁止修改旧输入；实际交付新增原文后修订候选并重新独立审核。输入转换和来源进入运行配置，strategy 附件同步更新。

具体字段、命令、输出和限制见 [分项反馈与输入修订](stage4/REVISION.md)。这两项属于现有生成—审核—修订循环。

## 统一模型创建入口（2026-11-02）

各阶段通过 stage1/model_factory.py 的 ModelConfig、create_model 和 model_factory 创建适配器，每任务一个新对象，会话仍独立。保留现有模型参数、元数据、异常和隔离检查；无自动后端回退。本次不新增 Windows 适配，不改变库配置及图分析参数。

完整职责与入口覆盖见 [模型后端说明](MODEL_BACKEND.md)。

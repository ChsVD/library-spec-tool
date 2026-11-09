## 模块内候选规划（2026-10-20）

新实验先使用 `stage2/manifests/openssl-bn-module.json` 枚举 BN 模块，不能把旧的 `openssl-bn-word-group.json` 文件范围视为模块依赖排序结果。旧清单仅保留以复现历史实验。

运行 `python3 -m stage2.frontier --input input --manifest stage2/manifests/openssl-bn-module.json --output runs/<new-directory>`。可用 `--callee-contracts` 指定经过哈希校验的 QCP 接口登记表；只有配置精确匹配的接口才计入已处理依赖。`python -m stage2 --prepare-only` 遇到 module 清单也会输出该规划。

输出完整函数候选、调用边、待处理接口、条件实现和扫描缺口。候选按未处理依赖数排序；宏、间接调用、同名多实现及未解析源码不能被当作依赖已解决。相互递归的函数因未处理调用保持阻塞，不自动放行。零已识别调用仅表示值得审核，不表示类型、配置或证明环境就绪。所有推荐仍待用户审核，本步骤不会自动生成执行清单或启动模型/证明；确认范围后才进入独立源码准备步骤。

当前采用现有保守 C 词法索引，未实现完整预处理、链接解析或 tree-sitter。汇编/生成源码等未覆盖项保留在 inventory_gaps；后续使用语法解析器缩小这些缺口。本轮 BN_add_word 人工适配文件独立保留，不会被原始模块扫描覆盖。

# 阶段 2 使用说明

> 2026-10-20 当前流程：独立源码提取（每函数一个.c，含callee声明及已有QCP规约、宏和依赖）→人工审核/适配→固化版本→自然规约生成与审查。默认阶段2要求`--prepared-source`，不再自动提取或补包；callee规约缺失返回准备步骤，不读取其完整实现推断。命令与审核约定见[源码准备流程](../SOURCE_BUNDLES.md)。下文涉及自动提取、自动补包的描述为历史设计。


当前默认采用源码包流程（`--workflow bundles`），详见[源码包流程](../SOURCE_BUNDLES.md)。下述历史真实测试使用旧流程，不代表新流程已完成真实验证。

本版以模块或完整函数组为选择单位，自动枚举范围内函数，再按函数生成自然规约、独立审查、有限修订及持久恢复。默认使用现有 Codex 登录，模型为 `gpt-6.1-sol`、推理强度 `high`。已完成一次真实 BN 单函数测试并通过独立模型审查，见[测试报告](../runs/stage2-real-sol61-high-20261018-01/TEST_REPORT.md)。结果是明确环境条件下的候选，仍未形式证明，人工验收和实际配置确认尚未完成。

## 图怎样控制上下文

`graph.json` 是运行中的函数记录。节点以唯一 ID 区分路径、函数和配置，保存自身候选规约、修订号、检查状态及原文入口。调用边从调用者指向被调用者，按调用点保留条件和需求。需求中的前提与保证作为一个场景保存，状态始终为 `required_not_guaranteed`，不会变成下层已证明保证。

每次模型会话只负责一个函数。初始上下文包含该函数身份、一跳调用关系、邻居状态与源码入口、调用点需求；相邻函数规约通过 artifact 按需读取，不注入整图或传递依赖的全部实现。模块说明与比较材料每 6000 字符分页提供，规约与审查任务通过 Reader 只读取已提取的源码片段；仅提取子任务可读取原库。所有这些读取都受会话总预算约束。

局部导航图默认上限 18000 字符，会话默认上限 60000 字符。规约与审查任务的完整报告上限为12000字符，修订与控制反馈另外预留8000字符；支持分字段保存报告和最终整体校验。完整关系详情按需读取，见[上下文与收尾政策](../SOURCE_BUNDLES.md)。高扇入/扇出使局部关系超限时明确停止，保留已有工作，不静默丢弃调用者。这版没有自动把单个巨大函数或高扇入节点继续拆分为子任务。

每个函数独立执行“源码提取 → 规约起草 → 局部审查”，不再等待整组调用关系发现完成。`--batch-size` 控制一次调度多少函数，`--concurrency` 控制并发数。每个角色使用独立模型会话，结果及时落盘。整组处理后，根据汇总调用图和最新邻居候选再独立复查；调用环内规约仍是假设，不构成递归一致性证明。调用图分层作为保存的分析结果，当前默认流程不以全图分层完成作为起草前置条件。

发现的范围外邻居只进入上下文，不自动扩大待写规约范围。v2 manifest 提供模块或函数组的文件/目录边界，不接受手写函数白名单。工具先枚举边界内的全部函数定义，建立待处理清单，再发现调用关系。没有调用联系的函数同样保留，依赖图只影响执行顺序。`--batch-size 1` 仍会依次处理整组。

当前示例选择 `bn_word.c` 的完整函数组，自动得到 `BN_mod_word`、`BN_div_word`、`BN_add_word`、`BN_sub_word`、`BN_mul_word`。这只是 BN 的一个函数组，不等于整个 BN 模块。文件边界与排除理由仍须审核，自动枚举不能判断人工选择的边界是否符合完整模块职责。

枚举使用保守的 C 文本扫描，不执行预处理。条件分支定义分别保留，复杂声明、可疑宏生成代码和不支持的实现文件记为缺口；出现缺口时保存 `needs_scope_review`，在调用模型前停止。文件排除须逐个明确填写理由。它不是完整 C 解析器，不能保证识别所有宏生成实现；源码阅读和范围审查仍有必要。

## 开始运行

从项目根目录先做不调用模型的材料校验：

```bash
python3 -m stage2 \
  --manifest stage2/manifests/openssl-bn-word-group.json \
  --output runs/stage2-bn-word-inventory --prepare-only
```

这会核对材料哈希和阶段 1 保存的 input 快照，并写出 `INVENTORY.json`、`FUNCTION_INDEX.md`，列明全部函数、文件覆盖和缺口。预检和正式运行必须使用不同的新输出目录。不能把旧报告与变化后的实现混用。首轮运行命令沿用此前真实测试使用的 CLI 路径：

```bash
PATH=/usr/local/lib/stage1-codex-0.163.0/node_modules/.bin:/usr/local/bin:/usr/bin:/bin \
python3 -m stage2 \
  --manifest stage2/manifests/openssl-bn-word-group.json \
  --output runs/stage2-bn-word-run \
  --model gpt-6.1-sol --reasoning-effort high \
  --batch-size 2 --concurrency 2 --max-revisions 1 \
  --calls 24 --seconds 1800 --call-timeout 600 --context-chars 60000
```

`calls`、`seconds` 和上下文限制针对每个角色任务，而不是整次运行；生成、审查和返工各有独立任务。`max-revisions=1` 允许初稿后再改一轮。最终邻居复查如果发现新问题，会保留 `needs_revision`，不无限循环改写。源码与参考文件仅允许读取，不执行库内脚本或 QCP。

旧 v1 函数清单仅用于兼容历史试验，CLI 必须显式添加 `--allow-legacy-function-list --workflow legacy`；它不代表已经枚举整组。

## 保存、恢复与检查状态

- `graph.json` / `graph.md`：函数规约、调用关系、使用需求、修订号和当前检查状态；Markdown 提供简洁关系图。
- `selection_inventory.json`：范围边界、文件覆盖、枚举方法、预期函数和缺口。
- `selection_progress.json`：预期数、已审查数、待处理函数和丢失节点；只有整组全部通过且无枚举缺口才报告整组完成。部分失败不会把已完成子集当成整组。
- `schedule.json`：汇总调用图的调用环及层次分析。
- `examples/<id>/v<attempt>-<revision>/`：实现、依赖、可选参考材料及来源清单。
- `functions/<id>/candidate-*.json/.md`：每次完整候选，连同独立审查记录保留。正常收尾时另外写当前 `candidate.json/.md`。
- `tasks/<role-function-attempt>/`：独立对话、原文读取记录、草稿和检查点。完整候选生成前的中断结果也在这里。
- `SUMMARY.md` / `status.json`：正常收尾时的汇总与持续保存的执行状态。早期失败可能尚无 SUMMARY，应查看 status 和 tasks。
- `identity.json` / `input_snapshot.json`：本次范围、材料、模型及输入版本，用于恢复核对。

同目录恢复时在原命令增加 `--resume`。恢复须保持输入、材料、manifest 和模型身份一致，已完成的源码包和已审查候选复用；未完成函数重新开启有界会话；已保存的未接受候选可作为明确标记的修补材料交接，须重新读原文，不继承证据信用或检查状态。旧会话和草稿保留，尚未返回的推理无法恢复。`insufficient` 和 `tool_blocked` 不会因恢复自动变成成功，需要处理所报缺口后重新组织输入或运行。文件锁阻止两个进程同时写同一运行目录。

更新一个函数候选会使已审查邻居进入 `needs_recheck`。最终复查读取当前候选与相关调用点；不能沿用旧依赖下的通过状态。图和状态哈希不一致时恢复拒绝继续，需检查持久任务记录，不猜测哪份检查点正确。

`candidates_reviewed` 只表示本轮自然规约候选通过模型审查；所有规约仍是 `not_proved`。存在核心未知、原文缺失、审查失败、图覆盖未知或输入变化时不会发布此状态。数组等条件按适用性填写，不能为纯标量函数虚构内存条件。

## 代码与测试入口

`inventory.py` 枚举选择范围并核对完成覆盖；`graph.py` 维护图及局部视图；`bundled.py` 负责默认编排、保存及恢复；`source_bundle.py` 与 `bundle_reader.py` 负责源码包及限定读取；`pipeline.py` 保留历史流程；`contracts.py` 检查范围、证据和输出结构；`prompts.py` 定义关系发现、规约编写和独立审查任务。复用阶段 1 的 Reader、Codex 后端、任务预算和草稿保存，不修改阶段 1 默认流程。

`python3 -m unittest discover -s tests` 运行阶段 2 机制测试。夹具中的审查结果用于测试返工路由，不代表真实模型已经能稳定识别过弱或过强规约。

## FM-Agent 实现参考及差异

本次阅读固定在作者仓库提交 `341aed7a60262186a34dc0340283a099d3195951`，不是将当前实现行为全部归因于论文版本。参考了：

- [generate_topdown_layers.py](https://github.com/fmagent-project/FM-Agent/blob/341aed7a60262186a34dc0340283a099d3195951/src/generate_topdown_layers.py)：调用者/被调用者映射、调用环与分层调度。
- [generate_batch_prompts.py](https://github.com/fmagent-project/FM-Agent/blob/341aed7a60262186a34dc0340283a099d3195951/src/generate_batch_prompts.py)：调用者规约、对当前函数的期望及批任务上下文组织。
- [spec_generation_and_verification.py](https://github.com/fmagent-project/FM-Agent/blob/341aed7a60262186a34dc0340283a099d3195951/src/spec_generation_and_verification.py)：逐单元产物检查与待处理批次调度。

本项目独立实现，未复制其代码或引入依赖。这里增加了跨库证据及适配说明、独立审查、调用需求与保证分离、邻居修改后的复查和版本核对。调用关系目前由模型在限定范围内读取原文后提出，机器检查端点与引用，不是 Clang 生成的完整静态调用图；间接调用、配置分支和漏边仍须人工或后续分析核对。

## 真实测试后的修订

入边场景放在 caller_scenarios，出边需求放在 call_requirements；不能混用，未读场景只能保留为未知。规约校验失败后可用 patch_report 替换既有报告的部分顶层字段，完整合并结果仍经过相同校验，减少在收尾阶段重发整份正文。该动作不允许绕过证据检查。

对于图中阻止具体构建结论的配置未知，独立审查可逐字引用候选environment中的相关条件，并解释为何当前只交付条件候选；原未知不会被删除。核心行为冲突、未解析出边或缺失证据仍不能据此通过。真实运行和机制检查范围见上述测试报告。

## 整组选择修正的验证

130 项机制测试通过，覆盖批大小为 1 仍处理整组、无调用联系的成员、部分失败后恢复、范围缺口阻断和重复函数身份。实际源码预检已枚举上述五个函数，见[函数清单](../runs/stage2-bn-word-group-inventory-20261018-01/FUNCTION_INDEX.md)。本次没有调用模型生成这五个函数的规约；此前真实模型审查仅覆盖单函数。

## 自动继续生成公共内容

添加 `--with-common` 后，仅当本轮整组状态为 `candidates_reviewed` 才自动进入阶段三。`--common-output` 指定新的阶段三输出目录，默认在阶段二目录名后加 `-common`。继续使用相同模型与预算，逐函数提取需求后合并公共定义和 lemma 候选，再独立审查。阶段三未通过时整个命令返回未完成。详见 [stage3/README.md](../stage3/README.md)。

## 必读材料预交付与缺口状态

bundles 的写作与审查现在先由程序独立交付该角色的必读输入：主模块说明、目标实现、相关依赖与未知详情；审查还包含候选、已有邻居规约及其所需证据。主模块必读，其他参考背景按需读取。交付占用实际上下文预算，保留最终报告空间，不等于语义审查通过。

每个任务的 required_inputs.json 保存清单。材料缺失、必读输入超预算、报告新增未读证据或收尾时请求新材料会生成 material_gap.json，并标为 needs_material；查看其中 reason 和 pending_actions（若有）及报告草稿定位缺口。不能靠修改措辞消除证据要求；普通报告错误仍可局部修订。目前不会自动拆分必读范围或为新引用启动续读任务。context_policy 为 3，旧运行需要新目录复测。

## 最新审查流程

context_policy=4采用程序材料预检、独立规约质量检查、整体行为与每组最多4条调用义务的一致性检查，最终由程序汇总全部结果。已知材料缺口先补包，不启动综合语义审查；各检查有自己的上下文、输出和证据信用。详情以[SOURCE_BUNDLES.md](../SOURCE_BUNDLES.md)最后的分工审查说明为准，前文综合审查和policy=3属于历史流程。真实运行需新目录。

最新context_policy为5：宏包保存完整定义和未求值外围条件；已提交报告的包内未读引用可触发一次最多6000字符的补读，模型须重新核对。包外缺口、预算不足或再次缺读仍停止。详情见SOURCE_BUNDLES.md末节，evidence_completion.json记录补读结果。

最新context_policy=6：写作与分工审查支持report_part.append及batch_id，成功批次即时保存至report-parts.json；finish组装后统一校验。格式错误保存format-error-N.json并最多修复一次。当前整份报告长度上限保留。完整规则见SOURCE_BUNDLES.md末节。

最新context_policy=7：写作任务只交付一套关系详情，writer-schema共享路径、条件和宏定义，各边及使用场景仍独立。主模块和必要原文保留。第五轮保存包的离线预交付均已低于40000字符；完整模型运行尚待验证，详见SOURCE_BUNDLES.md末节及writer_context_metrics.json。

最新 context_policy=8：引用区间缺口先由原写作/审查子任务作一次有界判断与修订，程序仍严格核对实际已读证据；依赖行为缺口可用明确关联的 conditional_assumptions 进入独立审查，源码、调用图和宏展开缺口不能豁免。假设及原始缺口保留，后续公共内容也须逐项保留并审查条件。具体字段和边界见 [SOURCE_BUNDLES.md](../SOURCE_BUNDLES.md) 末节。此次没有执行新的真实模型批次。

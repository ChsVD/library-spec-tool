# 多目标函数组的需求范围

本流程读取已经完成的阶段二依赖图，不重新扫描源码或运行 FM-Agent。它记录供后续证明参考的依赖顺序，不启动模型或证明，也不声称函数已具备证明条件。

## 分组和边界

三种角色分别保存：
- target：用户指定目标、同一递归分量成员，以及向下补入的被调用依赖；全部交给阶段三规划公共内容。
- demand：为了向目标传递需求，需要生成规约的上层函数。
- context：与需求子图相邻、但不在本次生成范围内的边界背景。已有草稿不自动成为适用或已证明契约。

新版计划（version=2）先计算 SCC，并从用户目标沿调用方向向下展开，把所有已识别的被调用依赖纳入 target_ids。递归分量整体处理，共享依赖只加入一次。旧草稿、名称相同或已有 review=pass 都不能自动截断依赖；当前没有自动验证并匹配已证明契约的机制，因此默认继续纳入。

随后对扩展后的全部目标向上追溯需求。默认取全部祖先并集；指定 root_ids 时，只保留入口到扩展后目标的全部已识别路径。每个入口必须能到达用户原始目标，所有原始目标分量必须被入口覆盖。新增底层目标的其他调用分支也参与需求追溯；被入口边界截断的分支仍记录为未覆盖。

需求背景函数的其他辅助调用只作为边界，不因其提供需求背景而无限扩展整个模块。只有 target_ids 向下闭合。自然规约仍 caller-first；proof_order_components 给出 target_ids 的 callee-first 分量顺序，不启动证明，也不代表未知依赖已解决。

范围必须依赖具体函数 ID，不能只凭名称把平台或条件实现合并。配置未知、间接调用候选和原图枚举缺口继续保留。本步骤没有完成全构建配置验证。

范围外的出边作为辅助依赖保留；范围外进入子图的边记录为未覆盖的上层需求。指定入口并不意味着其所有调用者都已覆盖。目标的下层依赖默认进入生成任务；需求背景的辅助出边和显式排除的下层依赖仍保留边界，不以已有草稿作为自动截断依据。

## 1. 准备请求

请求 JSON：
```json
{
  "target_ids": ["图中的确切函数ID-A", "图中的确切函数ID-B"]
}
```

可选 root_ids 是同样格式的函数 ID 数组。省略表示反推扩展后目标的全部已识别祖先；不能用空数组表达“无上层需求”。若仅从目标自身开始，可将 root_ids 设为原始目标 IDs；其他调用者仍记录为边界。

确需把下层依赖留给其他批次时，可指定：
```json
{
  "target_ids": ["函数ID-A"],
  "root_ids": ["函数ID-A"],
  "dependency_boundaries": [
    {"function_id": "函数ID-B", "reason": "另批处理；契约适用性尚待核实"}
  ]
}
```
边界按整个 SCC 截断，不能排除用户目标所在分量，也不能填不可达或无理由的边界。若其他路径仍到达更底层函数，这些函数继续纳入。显式边界不授予契约可信度：依赖状态保持 unresolved，后续仍须提供匹配的已验证契约或回到该依赖补充处理。未知调用、条件候选及枚举缺口同样不能被当作“已到达叶子”。

旧版 version=1 计划仍按原祖先路径语义加载，历史摘要和范围不自动迁移。要启用向下展开，应创建新计划、审核新摘要并使用新的输出目录。

## 2. 生成待审核计划

```sh
python3 -m stage2.demand_scope \
  --input input \
  --graph-run runs/fm-agent-bn-module-graph-20261027-02 \
  --request path/to/request.json \
  --output runs/new-demand-plan
```

输出：
- scope-plan.json：requested_target_ids（原目标）、target_ids（完整处理组）、scc_added_target_ids、dependency_added_target_ids、需求集合、显式边界及理由、目标未知调用、依赖状态、建议证明顺序、来源摘要和 plan_digest。
- SCOPE.md：可阅读的范围清单及边界调用，供人工审核。
- graph.json：裁剪后的可视化/检查材料。它不包含运行身份和审核状态，不能直接交给阶段三或作为 --graph-run。

计划绑定原 graph.json、来源清单及输入快照。修改目标或边界后重新规划；不通过手改摘要迁移旧计划。未知项不是缺失节点的替代证明。

## 3. 接入阶段二

先验证准备流程，不运行模型：
```sh
python3 -m stage3 \
  --manifest stage2/manifests/openssl-bn-module.json \
  --scope-plan runs/new-demand-plan/scope-plan.json \
  --output runs/new-group-specs \
  --prepare-only
```

确认 SCOPE.md 中的目标、SCC 新成员和边界后，执行时提供该计划的完整摘要：
```sh
python3 -m stage3 \
  --manifest stage2/manifests/openssl-bn-module.json \
  --scope-plan runs/new-demand-plan/scope-plan.json \
  --approve-scope <scope-plan.json中的plan_digest> \
  --output runs/new-group-specs \
  --resume
```

--approve-scope 表示运行者接受这份具体范围，不是图正确性的证明或模型语义审核。prepare-only 不需要此参数；从已准备运行继续生成时必须提供。默认独立模型审核保持启用。可以用 --max-components 限制单次处理量，再用同一计划 --resume；已经完成并审核的函数不会重复生成。

该模式要求 caller-first，不能与 --continue-from、--regenerate 或 --graph-compile-commands 组合。要改变编译配置，先生成新图再规划。manifest 必须与源图的清单一致，避免将其他模块材料误接进来。通过原 manifest 的模块说明与参考材料入口继续供给内容。

本次只实现同一计划内的增量推进和恢复；跨计划自动复用、按新增需求精确重算、递归分量内固定点协调尚未实现。新的计划从原始函数实现生成新草稿，不把源运行中的旧草稿直接继承为已审核结果。

## 4. 需求与调用点绑定

多目标模式中的 callee_requirements 必须指定：
- edge_id 和 callee_id：输入中本函数的确切出边和目标。
- callee：该边的符号名，用于可读性；不能替代 ID。
- callsite_indices：对应边 callsites 数组中的零起始下标。
- condition：该组调用点的条件/场景；不能把不同场景前提合取。
- requirement：该场景下的需求。

一条边可有多条场景需求。缺少调用点信息时使用空下标数组，并明确条件未知；无法解析成边的调用写入 assumptions。程序拒绝不存在的边、错误目标、越界调用点或缺失条件；独立模型审核进一步判断需求含义。结构校验不是语义完备性证明。

背景节点不会进入调度，但与当前任务相邻的背景实现、已有草稿及其未证明状态会提供给生成和审核。材料过大仍按现有预算明确失败，不静默截断。

## 5. 阶段三交接

阶段二整个 generation_ids 集合必须完成生成及配置要求的独立审核，再进入阶段三。可通过 --with-common 自动衔接。

阶段三：
- 对完整 target_ids（包括向下补入的依赖）做逐函数缺口提取及公共内容覆盖检查；
- demand 节点规约作为上层需求背景；
- context 节点及 boundary_edges 作为边界背景；
- 目标假设与上层背景假设分别记录，不能直接把上层前提变成目标统一前提；
- version=2 的 dependency_scope 同时交接原目标、补入依赖、未解决边界、未知调用及建议证明顺序；
- 所有自然规约和公共候选仍未证明。

## 历史 version=1 静态示例

runs/bn-demand-scope-preview-20261027-01 使用既有 BN 模块图中的 bn_add_words、bn_sub_words、bn_mul_words、bn_mul_add_words 在 bn_asm.c 内的全部已索引条件定义作为示例。4 个名称对应 7 个目标定义，另有 7 个上层需求定义、12 个边界背景定义及 36 条边界边。示例没有代表用户确认正式处理组，没有模型任务，也没有重建图。完整请求和计划可审核后重用。


## 历史验证记录

本轮全套回归 330 项通过（启用实际 FM-Agent 后端静态测试），随后补充同名 callee 边隔离用例，多目标专项 9 项全部通过。范围专项覆盖祖先并集合并、入口截断、SCC 补入、来源和计划漂移拒绝、范围确认、无重建图的准备/续跑、需求绑定及目标组阶段三交接。模型部分使用模拟模型；没有实际生成规约或证明。


## version=2 验证记录（2026-10-30）

范围专项 16 项通过；全套 unittest discover 共 350 项，347 项通过、3 项跳过。新增回归覆盖上层目标向下闭合、共享依赖的其他调用需求、递归分量完整性、旧草稿不能截断、显式边界与共享替代路径、未知调用保留、阶段二顺序及阶段三完整目标交接、version=1 历史范围兼容。模型部分使用测试替身，未启动实际模型、Coq 或 QCP。

对本轮已保存且经监督补过候选边的 BN 派生图做只读静态检查：以 BN_uadd、BN_usub 同时作为目标和需求入口，得到 10 个处理定义，其中补入 bn_add_words 两个条件定义、bn_sub_words、bn_wexpand、bn_expand2、bn_expand_internal、bn_free_d 和 BN_get_flags。该结果仅反映这份图，未修复图构建器；30 条目标未知记录及枚举缺口仍使依赖状态为 unresolved。历史图、计划和证明文件没有改写。

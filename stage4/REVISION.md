# 分项反馈与补充输入后的修订

这两项属于现有生成—审核—修订循环，不是新增阶段。

## 分项审查

使用 --component-review 启用。审核报告新增 item_reviews，按候选 ID 完整覆盖：

```json
{"item_id":"array-memory","verdict":"insufficient","reason":"未提供数组谓词定义",
 "action":"add_material","material_needed":"对应数组存储谓词和边界引理"}
```

verdict/action 对应关系：pass/retain、needs_revision/revise、insufficient/add_material。reason 必填，材料不足时还需 material_needed。按实际候选划分，不强制所有任务都分成数学与 QCP 两类。

部分候选通过、部分未通过时整体可为 partial。partial 不等于 common_candidates_reviewed，CLI 返回未整体通过，不自动交付完整公共库。通过只是设计审核通过，不是证明通过。

程序检查每项覆盖和依赖。通过项不能依赖未通过项；阻塞 finding 必须给出 item_ids。候选 blocking unknown 若没有 item_ids，保守视为影响全部候选；未解决需求也不能在分项结果中被隐藏。审核者仍须独立读取原文，所有原校验保持不变。

有 revise 动作时在现有 max-revisions 内继续修订；只有缺材料的 partial 会停止，等待显式补充输入。工具不自行下载材料或扩大输入权限。

## 输入修订

在新的输入目录保留全部旧文件，只增加明确列出的材料；输出使用新目录。程序不创建或擅自补充这些输入文件。

transition.json 的结构：

```json
{
  "version": 1,
  "baseline_root": "/absolute/original-input",
  "new_root": "/absolute/expanded-input",
  "source_stage3_run": "/absolute/spec-run",
  "added_files": [
    {"path":"foundation/Array.v","sha256":"完整文件SHA256","origin":"原仓库路径及版本"}
  ]
}
```

baseline_root 对应阶段三原输入，source_stage3_run 是阶段三规约运行。目录名不固定为 framework。新增清单必须精确覆盖相对原输入新增的全部文件，不能少报、多报或哈希不符。原文件禁止修改、删除；前一次输入修订已增加的文件也不能改动。

```bash
python3 -m stage4 \
  --input /absolute/expanded-input --stage3-run /absolute/spec-run \
  --revise-from /absolute/previous-common \
  --input-transition /absolute/transition.json \
  --component-review --output /absolute/revised-common
```

previous-common 必须是有一致检查点、完整提取和候选/审核记录的 partial、insufficient 或 needs_revision 运行；模型、目标范围及上游内容须匹配。不能拿未完成生成的报告当已审核修订基线，此类问题使用 recover-from。

程序复用已完成的需求提取，并把旧候选、审核反馈交给生成者。所有新增文件原文交付给生成者和新的独立审核者，按区间分段；缺失、二进制、无法读取或超过上下文预算时停止，不只发送文件路径就声称模型已读。源码包模式仍不能越过包的读取权限，新材料若不在包内会阻止交付。

执行者修订候选后重新导出 strategy 附件及索引，然后独立审核整份候选。当前不自动跳过“看似未受影响”的候选，也不沿用旧通过结论。结构差异记录不等于语义影响分析。

## 产物和恢复

新运行保存 input-transition.json、revision-seed.json、previous-candidate.json、previous-review.json，以及候选修订后的 candidate-change-N.json。后者记录新增、删除、变动和未变的候选 ID；独立审核仍覆盖全部候选。每次任务后复核旧输入、原运行文件及上游未变化。

既有 candidate.json、planning.json、review.json、reference_strategies/ 格式继续使用，review.json 增加分项反馈。输入转换、修订来源、分项审查开关写入运行配置。

修订运行中途停止后，保持输入转换及修订来源参数，可使用 resume；若恢复被拒绝的报告并写新目录，可同时指定 recover-from（失败的修订运行）、revise-from（原审核基线）及原 input-transition。不能更换转换记录来绕过一致性检查。

实现：[分项校验](components.py)、[输入校验](input_revision.py)、[执行循环](pipeline.py)。测试使用模拟模型，未证明真实模型能正确识别所有语义影响。

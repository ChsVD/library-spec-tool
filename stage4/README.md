# 阶段四：从已证明库筛选复用参考

## 当前入口与输入

阶段四现在可以直接接收默认阶段三生成的自然语言参考稿：

    python3 -m stage4 --stage3-run runs/reference-specs --output runs/common-candidates

也可以在默认阶段三完成后自动衔接：

    python3 -m stage3 --manifest stage2/manifests/openssl-bn-module.json --output runs/reference-specs --with-common --common-output runs/common-candidates

未指定 --common-output 时使用阶段三输出目录加 -common。只有本次选定范围内所有函数都生成草稿后才启动阶段四；计划模式不启动，部分完成时自动衔接命令返回失败并保留阶段三结果。阶段三范围可以是选定的函数组或继续运行确定的下层范围，不代表整个库。

新版输入不要求完整源码包；默认阶段三已启用独立模型审核，启用审核的运行必须全部通过才能交接。显式 --skip-review 和历史未审核参考稿仍可读取，但不会伪造审核状态。程序检查草稿完成状态、目标覆盖、必要字段、输入快照及可用的图摘要，拒绝已标记失效的结果。旧版普通参考稿也可读取；旧版继续运行若没有记录最终目标范围，需先用阶段三原参数加 --skip-review --resume 补齐元数据。已有旧流程的已审查结果仍按原门槛读取，不降低其检查要求。

新版参考稿区分未审核 reference_drafts 和已通过独立模型审核 reviewed_reference_drafts，两者均未证明；阶段四复用判断通过审查不升级上游状态。不会修改上游运行文件。

## 各角色实际收到的材料

提取角色读取本函数的完整规约和实现。整批汇总先收到由程序从提取报告生成的 `needs-summary`，需要核对完整条款或实现时再读取对应 artifact 或文件区间。独立审查收到候选、实际规约、实现及引用原文，可继续补读定义和使用位置。任务的 `conversation.jsonl` 可用于核对模型实际收到了哪些内容。离线执行 `python3 -m stage4.read_cost <阶段四运行目录>` 可统计各角色首包和后续交付；传入两个目录可查看两次运行的数据。计量单位为字符。策略和版本边界详见 材料交付说明。

## 输出与使用

每个函数产生一份 `functions/<函数ID>/common_needs.json`，保存实际存在的上游需求及由本轮规约提取的检索问题。整批共享同一套参考记录。每个函数保留自己的适配条件和不确定项。

下游从 `candidate.md` 阅读本轮结论，从 `candidate.json`、`planning.json` 和 `review.json` 获取原文坐标、使用位置和独立审查意见。没有找到内容时查阅检索范围。目标端仍需测试的边界可以和已认可的参考一同交付。相关 strategy 的原文及索引保存在 `reference_strategies/`。

`--resume` 用于配置不变的续跑，`--recover-from` 用于将停止任务恢复到新目录。新增输入须满足 输入修订 的清单和快照要求。报告长度可用 `--max-report-chars` 设置；上下文、时间和角色调用次数单独计量。跨协议重新运行请使用新目录。

详见 [输出协议](COMMON_CONTENT_TEMPLATE.md)、恢复 和 [开发指南](../DEVELOPMENT.md)。

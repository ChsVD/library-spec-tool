# library-spec-tool

根据一个待证明库及若干已证明参考库，选择模块和函数，生成自然语言规约，整理可供 QCP 使用的复用参考。

| 阶段 | 入口 | 产物 |
|---|---|---|
| 模块划分和比较 | python3 -m stage1.multi | 模块说明、跨库比较和推荐模块 |
| 函数依赖图和函数组选择 | python3 -m stage2；python3 -m stage2.select | graph.json、selection.json、scope-plan.json |
| 自然语言规约 | python3 -m stage3 | 逐函数推荐规约和审核记录 |
| 已证明库参考整理 | python3 -m stage4 | candidate.json、planning.json、review.json、candidate.md、strategy 原文附件 |

在 Ubuntu-24.04 WSL 中使用。各命令的具体参数见 --help。[开发指南](DEVELOPMENT.md)描述输入、输出和维护计划，[规约书写规范](SPECIFICATION_WRITING_GUIDE.md)规定语义和交接要求。

stage1 至 stage4 保存程序，templates 和 TASK_STAGE1*.md 是程序读取的提示与结构模板，tests 保存离线回归用例。input 保存当前可用的目标库和参考库。构图依赖位于 .deps 和 .venv-graph，可通过 scripts/setup_graph.sh 配置。

examples/simplex-int 保存 int 版单纯形实验的 C、头文件、Rocq 和相关规则源文件，沿用原有相对目录。target 是原始源码，contracts 是接口规约，checks 和 generated 含准备及待标注材料，qcp/QCP_examples 与 qcp/Rocq/examples 保存标注和证明源码。调用测试及验收日志已经清理；重验需要独立配置 QCP 环境。

运行产物默认写入 runs，目录按需新建。执行离线回归：

    python3 -m unittest discover -s tests -q

后续 QCP 任务还须交付[QCP strategy 书写规范](QCP_STRATEGY_GUIDE.md)，与规约书写规范一并阅读；具体交接要求见 [AGENTS.md](AGENTS.md)。


## 配置阶段一的目标库与参考库

任意库集合通过 `--library-config` 明确指定角色，例如 `libraries.json`：

```json
{
  "target_library": "solver",
  "reference_libraries": ["arithmetic", "collections"]
}
```

原始材料分别放在 `input/solver/`、`input/arithmetic/`、`input/collections/` 下。ID 使用小写字母、数字、连字符或下划线，以字母或数字开头，最多 80 字符；目录不得使用符号链接。参考列表可以为空。以下命令会运行模型：

```bash
python3 -m stage1.multi --input input --library-config libraries.json --output runs/new-module-selection
```

配置文件路径相对于命令执行目录，材料路径相对于 `--input`。每个角色收到相同的库角色配置；运行保存 `library_config.json`，结果仍需用户审核。省略参数时兼容原 OpenSSL / SM2 / mini-GMP 输入，不自动推断新库的角色。阶段二继续使用选定模块的 manifest。

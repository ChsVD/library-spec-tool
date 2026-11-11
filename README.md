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

# 整库规约工具 v2

本分支提供三个阶段：构建库内函数调用图、生成逐函数自然语言规约、检索参考并生成公共定义、引理和 strategy。各阶段通过 JSON 交接；阶段三将独立审核结论、内容覆盖和目标端验证状态分开记录。

- [运行环境、CLI 与程序接口](PROGRAM_REQUIREMENTS.md)
- [阶段三开发方案](STAGE3_DEVELOPMENT_PLAN.md)
- [阶段三生产验收结果](runs/stage3-acceptance-20261119/ACCEPTANCE.md)
- [Minimal Simplex 隔离样例](example/minimal-simplex)

在 Linux 或 WSL 的仓库根目录运行 `python3 -m stage1 --help`、`python3 -m stage2 --help` 或 `python3 -m stage3 --help` 查看参数。阶段一真实构图的依赖安装见 `scripts/setup_graph.sh`。

随分支发布的历史运行记录保留原始路径和摘要。涉及冻结输入的集成测试按原实验目录 `/home/maxu/Projects/library-spec-tool-v2` 解析材料。新的分析运行会记录实际使用的路径。

# 阶段 0 输入材料

整理日期：2026 年 10 月 18 日。

本目录保存本地工作文件的独立副本，原目录保持不变；复制时排除 .git 历史，保留原有实现、文档、规约、引理、证明及 strategy 文件。保留 strategy 不表示本阶段开展策略提取。

- openssl/：待证明库，来源 /home/maxu/Projects/openssl，复制整个源码工作目录。
- sm2/：参考库，来源 /home/maxu/Projects/sm2，包含 annotated_C、rocq、docs 和 test 等原目录。
- mini-gmp/：GMP 参考材料，来自 /home/maxu/Projects/QCP_maxu 中的 minigmp 验证案例，保留 QCP_examples/Applications_human/minigmp 和 Rocq/examples/Applications_human/minigmp 路径。它不是完整 GNU GMP；包含 C 实现、规约、GmpAux.v、GmpNumber.v、GmpMulAux.v、手工及自动证明和原有策略文件。

SOURCES.json 保存来源路径、仓库 HEAD、所选来源路径的工作区状态以及逐文件 SHA-256。普通文件已经与来源逐一校验，符号链接按链接目标校验。仓库 HEAD 仅标识基线，具体输入以复制文件及其哈希为准。

本次仅整理输入，未重新验证来源证明。mini-gmp 所需的 QCP 公共依赖及完整运行环境尚未单独打包；后续按依赖补齐。阶段 0 不预选试验模块。阶段 1 由工具分析模块并提出推荐，用户审核后再确定模块专用需求、运行配置和验收样例。当前还需明确整体分析目标与材料边界。

复制结果：

- openssl：6201 个文件或链接，138309957 字节；HEAD `5f61ae81549a6872869469bcb2784cdc08be9271`。
- sm2：681 个文件或链接，41995022 字节；HEAD `185efb11e0d0f6f55a41d8317b7e7f7e2c983336`。
- mini-gmp-c：3 个文件或链接，41127 字节；HEAD `fc37ed44f9ac3142c85499f6d0752dc7768695cc`。
- mini-gmp-rocq：16 个文件或链接，1077556 字节；HEAD `fc37ed44f9ac3142c85499f6d0752dc7768695cc`。

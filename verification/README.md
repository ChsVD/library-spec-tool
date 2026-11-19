# 优化版 Simplex 的规约与证明

本目录保存固定五项优化全开版的原版 QCP 验证材料，采用 Arch32 BigEndian 和 Coq 8.20.1。公开需求见[输入契约](../INPUT_CONTRACT.md)。顶层规约见 [sx_check_qcp](QCP_examples/Applications_human/simplex_gmp_optimized/sx_check_qcp_opt.c)，公共尺寸谓词和推导引理见 [build_opt_lib.v](Rocq/examples/Applications_human/simplex_gmp_optimized/build_opt_lib.v)。

- `QCP_examples/` 保存七个目标函数及分离求余包装的最终标注 C，附带所需头文件和 strategy。
- `Rocq/` 保存各案的义务、人工证明和案例库，以及这些文件直接或间接导入的项目级 GMP 和 minimal Simplex 模型。
- [验收索引](receipts/index.json)记录案例、原版控制器的终验回执、求解器与工具哈希，以及所需 QCP 核心库文件的指纹。
- `SHA256SUMS` 可用 `sha256sum -c SHA256SUMS` 核验本目录的归档文件。

将这两个目录按相对路径合入与验收索引匹配的原版 QCP 工作区，再使用该工作区的 QCP 构建与验证流程。原版验收口径为控制器 `final-check` 通过并进入 `done`。生成的 `*_proof_auto.v` 保留了原版流程的自动侧义务和占位，人工证明见相应的 `*_proof_manual.v`。

`normalize` 的验证副本将三个单元素 `mpz_t` 局部数组改写为同型标量并显式取地址。运行库保留实验目标源码的 `mpz_t` 写法。验收结论覆盖在外部服务与后端容量前提下的正常返回。

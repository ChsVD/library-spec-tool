# SM2 验证

本仓库用于保存 SM2 实现的 QCP/Rocq 验证文件。

## QCP 版本

验证使用 [qcp-binary-democases](https://bitbucket.org/WxWyashen/qcp-binary-democases/src/main/)
仓库的 `main` 分支。

当前验证文件对应 QCP `main` 分支的 commit：

`126de54aacf08cd1caefe747383b7cfb3ab16a46`（短哈希：`126de54a`）

## 目录结构

- `annotated_C/`：带 QCP 标注的 C 源文件、头文件和 strategy 文件。
- `rocq/lib/`：表示谓词、数学规格和辅助引理。
- `rocq/strategy/`：strategy soundness 的 goal、proof 和最终检查。
- `rocq/vc/`：符号执行生成的目标，以及自动证明、手工证明和最终检查。
- `rocq/Makefile`：部署到 QCP 后的生成、单 case 检查和全量编译入口。
- `docs/`：验证设计说明以及验证进度记录。
- `test/spec_check.py`：检查生产函数签名、base/derived contract 和 caller 副本。

## 仓库用途

本仓库记录 SM2 生产调用链及其 SM3 依赖的正式验证 artifact。当前 `main`
分支包含 89 个已完成 C case、40 份 strategy 及其 soundness proof，以及 33 个
Rocq 库文件。89 个 case 按模块分布为：`basicOp` 18 个、`fieldOp` 22 个、
`ecc` 17 个、`ecc_montg` 17 个、`extra` 2 个、`sm2` 8 个和 `sm3` 5 个。

将 `annotated_C/` 和 `rocq/` 分别同步到 QCP 的
`QCP_examples/Applications_human/sm2/` 与
`Rocq/examples/Applications_human/sm2/` 后，在后一个目录使用 Makefile 生成或编译。

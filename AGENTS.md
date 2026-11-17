# 函数验证的规约规范与交接

每次生成自然规约、通用内容、形式化规约或验证函数时，必须使用[规约书写规范](SPECIFICATION_WRITING_GUIDE.md)。主 agent 在每次任务的初始交接中明确提供该文档的绝对路径，交给相关生成、annotation、独立审查和证明 agent；要求先阅读后工作，不能仅凭历史对话中提到过而省略。

当前绝对路径：`/home/maxu/Projects/library-spec-tool/SPECIFICATION_WRITING_GUIDE.md`。

文档是持续维护的统一入口。新隔离环境继续传入此路径；若迁移导致不可访问，应提供同版本副本并标明来源。每次结果记录规范版本、本轮命名规约、实际调用检查状态及未覆盖情形。所有文件改动和工具操作继续遵循各验证仓库的 AGENTS.md 与 QCP controller 工作流，本文不扩大 agent 的写入权限。

尤其要检查：需要分别调用的资源状态采用 QCP 命名规约；调用者分支作用域正确；不能把自身函数证明通过当作调用匹配通过。具体规则及已经验证的例子见规范正文。

## QCP strategy 规范交接

后续将任务交给 QCP agent（包括 annotation、strategy 编写、审查和证明）时，必须同时提供[规约书写规范](SPECIFICATION_WRITING_GUIDE.md)和[QCP strategy 书写规范](QCP_STRATEGY_GUIDE.md)，要求先阅读再工作。

Strategy 规范固定路径：`/home/maxu/Projects/library-spec-tool/QCP_STRATEGY_GUIDE.md`。隔离环境无法读取此路径时，提供同版本副本并记录来源及 SHA-256；交接记录注明实际使用的版本或摘要。该文档来自用户于 2026-11-12 提供的 `QCPStrategy(1).md`，原文保存。

这项交接要求不扩大阶段四职责：阶段四仍筛选已有相关 strategy；新规则的设计、安装和验证由后续 QCP 流程按其权限与检查要求执行。

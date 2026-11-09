# 函数验证的规约规范与交接

每次生成自然规约、通用内容、形式化规约或验证函数时，必须使用[规约书写规范](runs/isolated-bn-words-sol61-high-20261020-01/evaluation/SPECIFICATION_WRITING_OPTIMIZATION.md)。主 agent 在每次任务的初始交接中明确提供该文档的绝对路径，交给相关生成、annotation、独立审查和证明 agent；要求先阅读后工作，不能仅凭历史对话中提到过而省略。

当前绝对路径：`/home/maxu/Projects/library-spec-tool/runs/isolated-bn-words-sol61-high-20261020-01/evaluation/SPECIFICATION_WRITING_OPTIMIZATION.md`。

文档是持续维护的统一入口。新隔离环境继续传入此路径；若迁移导致不可访问，应提供同版本副本并标明来源。每次结果记录规范版本、本轮命名规约、实际调用检查状态及未覆盖情形。所有文件改动和工具操作继续遵循各验证仓库的 AGENTS.md 与 QCP controller 工作流，本文不扩大 agent 的写入权限。

尤其要检查：需要分别调用的资源状态采用 QCP 命名规约；调用者分支作用域正确；不能把自身函数证明通过当作调用匹配通过。具体规则及已经验证的例子见规范正文。

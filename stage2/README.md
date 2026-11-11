> **适用范围**：本阶段面向一个待证明库和若干个已证明参考库。下文 OpenSSL BN、SM2、mini-GMP 及相关路径是当前案例；参考库数量不限定为两个。通用设计与当前实现限制见 [开发指南](../DEVELOPMENT.md)。

# 阶段二：函数依赖图与函数组选择

输入为已选定模块的 manifest、原始源码和编译配置；输出为函数定义、调用关系、未知调用，以及本轮函数组、需求调用者、范围边界和处理顺序。本阶段不生成自然语言规约。图和范围计算不调用模型；可选选择会话由模型判断功能价值，由静态工具计算依赖和预算。

## 命令

运行命令时位于项目根目录：

~~~bash
python3 -m stage2 --input input --manifest stage2/manifests/openssl-bn-module.json --output runs/new-graph
python3 -m stage2.demand_scope --input input --graph-run runs/new-graph --request request.json --output runs/new-scope
~~~

图准备输出 graph.json、identity.json、status.json 和 SUMMARY.md；范围选择输出 scope-plan.json、SCOPE.md 和投影后的 graph.json。初始 target_ids 可由用户指定，也可由 stage2.select 在单个会话中读取原文并提出；不保证全局最优。用户确认范围后使用 python3 -m stage3 生成自然语言规约。

--prepare-only 是兼容参数：阶段二无论是否提供该参数都只做静态准备。自然规约生成参数不再由这个入口接受。

## 代码与兼容性

- fm_graph.py、fm_graph_worker.py、inventory.py：源码分析与函数图。
- demand_scope.py、graph.py：处理范围、SCC 与调用图操作。
- manifests/：模块输入清单。
- prepare.py、legacy_cli.py 等旧源码准备实现暂时保留，不属于默认阶段二执行链。
- reference.py、reference_review.py、read_materials.py、scenario_guidance.py 仅为旧 Python 导入提供兼容转发，实际实现位于 stage3/。
- 图准备暂复用 stage3.reference.run 的 prepare_only 分支，以保持已有图文件格式；入口不创建模型，并提供禁止模型调用的回调。

详细说明：图后端、范围选择、[开发指南](../DEVELOPMENT.md)、[自然语言规约](../stage3/README.md)。

## 可选的函数组选择

python3 -m stage2.select 使用单个会话沿图向上选择，依赖和预算通过静态工具查询。详细参数、工具和产物见 函数组选择。

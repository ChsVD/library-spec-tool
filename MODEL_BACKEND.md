# 统一模型创建入口

所有现行阶段及兼容 CLI 通过 stage1/model_factory.py 创建模型适配器。此次只整理已有 Codex（Linux/WSL）和阶段一显式 API 后端，不增加 Windows 适配，不修改库配置或图分析参数。

```python
config = ModelConfig(model="gpt-6.1-sol", reasoning_effort="high")
factory = model_factory(config)
writer = factory("common", "common-0001")
reviewer = factory("review", "review-0002")
```

每次 factory 调用创建新对象，生成、审核、修订的会话仍由 run_task 或 ReadingModel 独立管理。factory 同时接受阶段三的单 ID 回调和其他阶段的 role/task_id 回调；这些标识用于调用兼容，不用于共享模型对象或历史。

## 职责

- ModelConfig 保存后端、模型和推理强度；API 的现有环境变量在创建配置时读取，避免同一工厂的不同任务受到后续环境变量改变影响。
- create_model 按显式配置构造现有适配器；不自动切换后端，不发送模型请求。
- model_factory 返回每任务创建函数。需要预检的入口仍先创建一个对象，预检不代表已执行模型任务。
- 参数默认值继续由现有 CLI 提供；阶段一仍可继承 Codex 配置，后续阶段仍保留各自原有默认模型和推理强度，本次不统一改变这些默认值。
- 任务预算、原文读取、报告修复和独立审核仍由原执行器负责。静态阶段二和阶段三 prepare-only 不调用模型工厂。
- 原适配器的 metadata、异常类型、认证方式、隔离检查及恢复记录格式保持不变，不因为入口统一而重写旧运行身份。
- 不记录 ModelConfig 的 API 密钥；配置对象的 repr 隐藏该字段。不得把整个配置直接序列化进日志。
- Codex 预检失败仍明确报错，不回退到 API，也不降低 bubblewrap 隔离要求。

## 入口覆盖

stage1.multi、旧 runner 入口、continue_saved、smoke；stage2.select、旧源码准备与 legacy CLI；stage3.reference；stage4 CLI。stage3 的 --with-common 同样经过统一工厂。

阶段一原有 --backend api 保留；不为其他阶段额外增加 API CLI 开关。库角色、输入目录和编译配置通用化属于另一项工作，不在此次变更中。

实现：[model_factory.py](stage1/model_factory.py)。本次测试使用模拟适配器，不执行真实模型、网络 API 或 Windows 启动。

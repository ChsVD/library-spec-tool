# 阶段三生产入口验收

验收对象为 `python3 -m stage3` 的 A 方案入口。生成、修订和独立审核使用 GPT‑6.2 Sol，推理强度 high。参考索引在每次启动时本地建立。模型只能通过程序提供的只读接口取证。结果目录的 `stage3.json` 可核对需求、逐轮审核、引用坐标、读取范围、用量和待验证条件；同目录 Markdown 供人阅读。

## 真实模型的抽样

六次独立运行均完成生成与审核，四次部分覆盖、两次完整覆盖，合计 33 次模型请求。每次只处理指定需求，因此任务状态可能显示仍有其他需求待处理。配置真实图后端后，完整单元与集成测试共 26 项通过，无跳过。

- [Simplex 原始 build 定义需求](simplex-final/stage3.md)。直接使用冻结的阶段二结果，在 60 条中选择第一条输入表示需求。结果引用 FME 的 Rocq 声明和 C 规约，保留两个复制位置的条件、静态 dummy 共享与清理和目标平台适配缺口。独立审核接受部分覆盖。

- [BIGNUM 表示](bignum-final/stage3.md)。使用历史规范化 C 探针，重新构图并生成阶段二规约。该探针只返回数据指针，此次阶段二未主动提出公共内容需求。因此为评测固定地加入既有 A/B 的 Q2，单独保存为 [frozen-q2.json](bignum-stage2/frozen-q2.json)。检索端面对完整的 MiniGMP 与 SM2 快照（690 文件）。模型读到 MiniGMP 的四条声明，说明了长度、符号、已用前缀及剩余容量的对应，列出元素表示、机器字宽和内存权限的缺口。仍未引用 SM2。审核通过，部分覆盖；该用例检验历史表示问题，未运行完整 OpenSSL 库。
- [Simplex 只有目标源码与规约](rule-source-only/stage3.md)与[另加历史 QCP 状态](rule-with-state/stage3.md)。使用冻结的链表重建题作为受控的 strategy 需求，绑定到实际 `build` 及第 97–104 行。前者识别到 FME 规则 12，但仅在右侧有相应非空链表目标时建议使用。后者读到真实生成的 `build_safety_wit_4`，指出前件已有两处字段和尾段，后件只要求整数范围，规则 12 无法在这个证明点触发。两份结果均部分覆盖。[状态摘录](historical-build-state.md) 取自旧工作区 `isolated-simplex-agent-eval-20261117-01/work/simplex-eval/diagnostics/record-builtins/build_table_goal.v` 第 87–115 行。
- [Yices 算术迁移](transfer-final/stage3.md)。从独立的 Yices `gcd32` 源码出发，用真实阶段一和阶段二生成三条需求。为测试“有参考”路径，在已有引理需求末尾加上一句要求查阅算术参考，独立保存 [lookup-check.json](transfer-stage2/lookup-check.json)。检索端使用来自本机 Rocq 标准库的 22 个自然数算术文件，引用 `NGcd.v` 和 `NParity.v` 中三条声明，区分数学化简与无符号位操作。审核给出完整覆盖。复用同一命令加 `--resume` 后仍累计 5 次模型请求。
- [Yices 空参考](no-references/stage3.md)。使用原始阶段二定义需求，省略参考清单。工具依据目标材料生成自然语言结果，通过独立审核；检索引用为空。此测试和有参考测试分别使用定义与引理需求，不能据此作两种输入的效果对照。

这里的完整或部分覆盖是对自然语言交付物的审核结论。所有具体用途保留 `target_validation=not_run`。验证环境和模型能支持的结论限于本次输入及阅读额度。

## 调度与故障回归

使用固定模型在 60 条原始 Simplex 需求上分别提交 17 条、续跑 43 条、再续跑同一目录。每条返回明确缺口，累计 120 次生成及审核请求，第三次启动无需请求模型。该项验证整批调度、保存、空结果和幂等恢复；抽样之外的需求未在本次接受真实模型的语义评审。[调度验收脚本](check_schedule.py)

真实数据暴露了嵌套 `:=` 导致索引中断、检索返回过长以及调用记录挤占首包的问题。修正后重跑。最初的失败记录分别留在 `bignum-real` 和 `simplex-real`。另有固定响应回归覆盖未读引用、实际证据变更后续跑、审核退回修订与跨位置共享；原单文件离线 CLI 已输出 [回归结果](offline-regression.json)。

从工具根目录复核回归：

```bash
LST_RUN_GRAPH_TESTS=1 LST_DEPS_ROOT=/home/maxu/Projects/library-spec-tool python3 -m unittest discover -s tests -v
PYTHONPATH=. python3 runs/stage3-acceptance-20261119/check_schedule.py
```

复现实模型验收时，输出用新目录。以跨库引理题为例：

```bash
r=runs/stage3-acceptance-20261119
python3 -m stage3 --stage2 "$r/transfer-stage2/lookup-check.json" \
  --need-id 'fn-a2ff99ca89c05de1e608dc65:2:c37e85dee95e6da2' \
  --references "$r/transfer-references.json" --output "$r/transfer-replay" \
  --model gpt-6.2-sol --reasoning-effort high --timeout 900 \
  --max-files 3 --max-reads 6 --max-requests 30
```

阶段二结果绑定本机阶段一快照；参考清单中的绝对路径对应此次验收环境。模型回答与候选次序可能随运行变化。

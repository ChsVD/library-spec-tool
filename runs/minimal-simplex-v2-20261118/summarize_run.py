"""Summarize a saved natural-contract run without influencing either model."""
from collections import Counter
import json
from pathlib import Path

root = Path(__file__).resolve().parent
parts = ["# 自然规约运行结果", ""]
for label,key in [("原样调用图试验","native"),("链接证据主试验","link-evidence"),("报告规则澄清后续跑","link-evidence-clarified")]:
    result = root / f"stage2-{key}" / "stage2.json"
    if not result.is_file():
        continue
    state = json.loads(result.read_text())
    upstream = json.loads(Path(state["stage1_result"]).read_text())
    funcs = state["functions"]
    nodes = upstream["graph"]["nodes"]
    selected = state["scope"]["function_ids"]
    status = Counter(v["status"] for v in funcs.values())
    event_path = root / f"stage2-{key}-events.jsonl"
    last = None
    calls = Counter()
    if event_path.is_file():
        for line in event_path.read_text().splitlines():
            try:
                last = json.loads(line)
            except ValueError:
                continue
            if last["event"] == "model_call_end":
                calls[last["role"]] += 1
    parts.extend([f"## {label}", "",
                  f"- 状态 {state['status']}，已保存 {len(funcs)}/{len(selected)} 个函数。",
                  f"- {sum(bool(r.get('draft')) for r in funcs.values())} 份规约草稿。审核分布 {dict(status)}。",
                  f"- 模型完成调用次数 {dict(calls)}，接受补图 {len(state['accepted_edges'])} 条。",
                  f"- 形式化调用验证 {state['formal_call_validation']}。",
                  f"- 产物 [stage2.json](stage2-{key}/stage2.json)，[运行事件](stage2-{key}-events.jsonl)。", ""])
    if key=="native":
        parts.extend(["已保留入口记录并手动结束原样试验，后续使用链接证据输入。", ""])
    if last and last["event"] == "pipeline_error":
        parts.extend(["最后错误 " + last["error"], ""])
    parts.extend(["| 函数 | 审核状态 | 规约情景 |", "| --- | --- | --- |"])
    for ident in selected:
        record = funcs.get(ident, {})
        cases = (record.get("draft") or {}).get("cases", [])
        parts.append(f"| {nodes[ident]['name']} | {record.get('status', '未提交')} | " +
                     "、".join(case["name"] for case in cases) + " |")
    parts.append("")
    for ident,record in funcs.items():
        if nodes[ident]["name"]=="sx_check_qcp" and record.get("draft"):
            parts.extend(["### 入口规约", "", record["draft"]["purpose"], ""])
            for case in record["draft"]["cases"]:
                parts.extend(["#### "+case["name"], "", "With  "+case["with"], "",
                              "Require  "+case["require"], "", "Ensure  "+case["ensure"], ""])
            parts.extend(["#### 审核意见", "", record["reason"], ""])
            break
    print(label,len(funcs),len(selected),dict(status),dict(calls),last)
output = root / "RESULTS.md"
output.write_text("\n".join(parts)+"\n",encoding="utf-8")


current = root / "stage2-link-evidence-clarified/stage2.json"
if not current.is_file():
    current = root / "stage2-link-evidence/stage2.json"
if current.is_file():
    state = json.loads(current.read_text())
    upstream = json.loads(Path(state["stage1_result"]).read_text())
    nodes = upstream["graph"]["nodes"]
    specs = ["# Minimal Simplex 自然语言规约", "",
             f"主试验 {state['status']}，已提交 {len(state['functions'])}/{len(state['scope']['function_ids'])}。",
             "", "按函数列出实际提交的规约及独立审核。形式化调用测试未运行。", ""]
    for stage in state["scope"]["components"]:
        for name in stage["functions"]:
            row = state["functions"].get(name)
            if not row:
                continue
            node = nodes[name]
            draft = row.get("draft")
            specs.extend([f"## {node['name']}", "",
                          f"状态 `{row['status']}`，函数 ID `{name}`，源码 `{node['source']['path']}:{node['source']['line']}`。", ""])
            if draft:
                specs.extend([draft["purpose"], "", draft["symbols"], ""])
                for case in draft["cases"]:
                    specs.extend(["### "+case["name"], "", "**With**", "",case["with"], "",
                                  "**Require**", "",case["require"], "", "**Ensure**", "",case["ensure"], ""])
                for key,title in [("assumptions","假设"),("uncovered","未覆盖情形")]:
                    if draft.get(key):
                        specs.extend(["### "+title, "", *("- "+text for text in draft[key]), ""])
            specs.extend(["### 审核意见", "", row["reason"], ""])
    (root/"SPECS.md").write_text("\n".join(specs)+"\n",encoding="utf-8")

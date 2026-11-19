"""Render the Stage 3 JSON handoff as a human-readable Markdown report."""

import os
from tempfile import NamedTemporaryFile


def cite(source):
    return f'`{source["path"]}:{source["start_line"]}–{source["end_line"]}`'


def bullets(lines, heading, values):
    values = list(values)
    if values:
        lines.extend(("", heading, "", *(f"- {value}" for value in values)))


def render(state):
    summary = state["summary"]
    lines = [
        "# 阶段三公共内容",
        "",
        f'已审核 {summary["by_status"].get("accepted", 0)} / {summary["total_needs"]} 条需求，'
        f'待处理 {summary["pending"]} 条，共享条目 {summary["shared_items"]} 项。',
        f'当前状态 `{state["status"]}`，模型请求 {summary["model_requests"]} 次，'
        f'参考原文读取 {summary["reference_read_chars"]} 字符。',
    ]
    if state["blocked_functions"]:
        lines.extend(("", "## 无可用草稿的函数"))
        for row in state["blocked_functions"]:
            lines.extend(("", f'- `{row["function_id"]}` {row.get("reason", "")}'))

    lines.extend(("", "## 逐需求交付"))
    for ident, need in state["needs"].items():
        original = need["original"]
        lines.extend(("", f'### {original["kind"]} · {original["use"]}',
                      "", f'`{ident}`', "", original["need"],
                      "", f'上游状态 `{need["status"]}`。{need.get("reason", "")}'))
        row = state["uses"].get(ident)
        if row is None:
            lines.extend(("", "待处理。"))
            continue
        lines.extend(("", f'处理状态 `{row["status"]}`，覆盖 `{row["coverage"]}`，'
                      f'结论 `{row["disposition"]}`，适用性 `{row["applicability"]}`，'
                      f'目标验证 `{row["target_validation"]}`。'))
        if row.get("scope"):
            lines.extend(("", row["scope"]))
        bullets(lines, "**共享条目**", (f'[{state["items"][key]["title"]}](#{key.replace(":", "-")})'
                                        for key in row["item_ids"]))
        call_locations = {call["call_id"]: call["site"]["location"] for call in need["calls"]}
        bullets(lines, "**调用位置**", [f'`{key}` `{loc.get("path")}:{loc.get("line")}`'
                                      for key in row.get("call_ids", [])
                                      if (loc := call_locations.get(key))])
        bullets(lines, "**对象对应**", row.get("object_mapping", []))
        bullets(lines, "**使用条件**", row.get("conditions", []))
        bullets(lines, "**未解决事项**", row.get("remaining", []))
        bullets(lines, "**目标材料**", [cite(value) for value in row["evidence"]])
        bullets(lines, "**参考依据**", [f'{cite(value["source"])} {value["usage"]}'
                                     for value in row["references"]])
        if row.get("search"):
            search = row["search"]
            lines.extend(("", f'检索 `{search["status"]}`。{search["reason"]}'))
        if row["review"]:
            review = row["review"]
            lines.extend(("", f'审核 `{review["decision"]}`。{review["reason"]}'))
            bullets(lines, "**审核发现**", [f'“{f["quote"]}” — {f["request"]}' for f in review["findings"]])
            bullets(lines, "**上游复查**", review["upstream_questions"])
        if row.get("failure"):
            lines.extend(("", f'运行受阻。{row["failure"]["reason"]}'))
        for error in row["usage"]["read_errors"]:
            loc = error.get("location", error)
            label = cite(loc) if all(loc.get(key) is not None for key in
                                     ("path", "start_line", "end_line")) else loc.get("path", loc.get("id", ""))
            lines.extend(("", f'读取记录 {label}。{error["error"]}'))
        if row.get("uncommitted_draft"):
            for item in row["uncommitted_draft"]["items"]:
                lines.extend(("", f'**待复核候选 · {item["title"]}**', "", item["body"]))

    if state["items"]:
        lines.extend(("", "## 共享定义、引理和 strategy"))
        for ident, item in state["items"].items():
            lines.extend(("", f'<a id="{ident.replace(":", "-")}"></a>',
                          f'### {item["title"]}', "", f'`{ident}` · `{item["kind"]}`', "",
                          item["body"]))
            bullets(lines, "**依赖**", [f'`{key}`' for key in item["depends_on"]])
            for key in item["source_ids"]:
                source = state["sources"][key]
                lines.extend(("", cite(source), ""))
                lines.extend(f"    {line}" for line in source["text"].splitlines())
    return "\n".join(lines) + "\n"


def write_markdown(path, state):
    with NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as stream:
        temp = stream.name
        try:
            stream.write(render(state))
            stream.flush()
            os.fsync(stream.fileno())
            os.replace(temp, path)
        finally:
            if os.path.exists(temp):
                os.unlink(temp)

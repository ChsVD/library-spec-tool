"""Validate and normalize model reports before review and commit."""

from collections import Counter

from stage2.exchange import rows, text
from stage2.schedule import digest

from .exchange import location


KINDS = ("definition", "lemma", "strategy")
COVERAGE = ("complete", "partial", "uncovered")
DISPOSITIONS = ("direct_reference", "adaptation", "inspiration", "new_content", "gap")
CHECKS = ("direction", "target_conditions", "dependencies", "content")
DISCOVERY = ("list_files", "search_references", "list_entries", "related_entries")


def strings(record, key, *, unique=False):
    result = record.get(key)
    if not isinstance(result, list) or any(not isinstance(v, str) or not v.strip() for v in result):
        raise ValueError(f"{key} must be a list of nonempty strings")
    if unique and len(set(result)) != len(result):
        raise ValueError(f"{key} must contain distinct IDs")
    return result


def choice(record, key, allowed):
    result = text(record, key)
    if result not in allowed:
        raise ValueError(f"{key} must be one of {', '.join(allowed)}")
    return result


def source_ids(record, key, delivered):
    requested = strings(record, key, unique=True)
    unread = set(requested).difference(delivered)
    if unread:
        raise ValueError(f"{key} refers to evidence that was not delivered: {', '.join(sorted(unread))}")
    return requested


def validate_draft(report, tools, need):
    if not isinstance(report, dict) or report.get("need_id") != need["id"]:
        raise ValueError("draft must address the current need_id")
    coverage = choice(report, "coverage", COVERAGE)
    disposition = choice(report, "disposition", DISPOSITIONS)
    scope = text(report, "scope")
    remaining = strings(report, "remaining")
    conditions = strings(report, "conditions")
    mapping = strings(report, "object_mapping")
    calls = strings(report, "call_ids", unique=True)
    if set(calls).difference(c["call_id"] for c in need["calls"]):
        raise ValueError("call_ids must belong to this need's function")
    evidence = source_ids(report, "evidence_ids", tools.sources)
    references = {}
    for row in rows(report, "references"):
        ident = text(row, "entry_id")
        if ident in references:
            raise ValueError(f"duplicate reference {ident}")
        if ident not in tools.references:
            raise ValueError(f"reference {ident} was not delivered in this writer exchange")
        references[ident] = text(row, "usage")

    search = report.get("search")
    if not isinstance(search, dict):
        raise ValueError("search requires a status and reason")
    search_status = choice(search, "status", ("searched", "unnecessary"))
    available_searches = [*tools.trace.get("prior_search_scope", []), *tools.trace["actions"]]
    searched = any(row["action"]["tool"] in DISCOVERY and "error" not in row
                   for row in available_searches)
    if (search_status == "searched") != searched:
        raise ValueError("search status must match the successful reference discovery actions performed")
    search = {"status": search_status, "reason": text(search, "reason")}

    existing = tools.items
    items = {}
    for row in rows(report, "items"):
        ident = text(row, "id")
        if ident in items or ident in existing or ident.startswith("item:"):
            raise ValueError(f"new item requires a distinct local ID: {ident}")
        items[ident] = {
            "id": ident, "kind": choice(row, "kind", KINDS),
            "title": text(row, "title"), "body": text(row, "body"),
            "source_ids": source_ids(row, "source_ids", references),
            "depends_on": strings(row, "depends_on", unique=True),
        }
    requested = strings(report, "item_ids", unique=True)
    if coverage == "uncovered":
        if requested or disposition != "gap" or not remaining:
            raise ValueError("uncovered requires an explicit gap and no usable items")
    elif not requested or not evidence:
        raise ValueError("covered material requires items and delivered target evidence")
    if coverage == "partial" and not remaining:
        raise ValueError("partial coverage requires remaining obligations")
    if coverage == "complete" and (remaining or disposition == "gap"):
        raise ValueError("complete coverage cannot have unresolved coverage obligations")
    if disposition in ("direct_reference", "adaptation", "inspiration") and not references:
        raise ValueError(f"{disposition} requires delivered reference evidence")

    visited = set()
    active = set()

    def visit(ident):
        if ident in active:
            raise ValueError(f"item dependency cycle at {ident}")
        if ident in visited:
            return
        value = items.get(ident) or existing.get(ident)
        if value is None:
            raise ValueError(f"unknown item ID: {ident}")
        if set(value["source_ids"]).difference(references):
            raise ValueError(f"reread and cite the source IDs used by item {ident} in this exchange")
        active.add(ident)
        for dependency in value["depends_on"]:
            visit(dependency)
        active.remove(ident)
        visited.add(ident)

    for ident in requested:
        visit(ident)
    if set(items).difference(visited):
        raise ValueError("all proposed items must be used or reached through a dependency")

    return {
        "need_id": need["id"], "items": list(items.values()), "item_ids": requested,
        "disposition": disposition, "coverage": coverage, "scope": scope,
        "call_ids": calls, "object_mapping": mapping, "conditions": conditions,
        "remaining": remaining, "evidence_ids": evidence,
        "references": [{"entry_id": ident, "usage": usage,
                        "source": location(tools.references[ident])}
                       for ident, usage in references.items()],
        "search": search,
    }, {key: existing[key] for key in sorted(visited.intersection(existing))}


def string_leaves(value):
    if isinstance(value, dict):
        for entry in value.values():
            yield from string_leaves(entry)
    elif isinstance(value, list):
        for entry in value:
            yield from string_leaves(entry)
    elif isinstance(value, str):
        yield value


def validate_review(report, tools, draft, shared):
    if not isinstance(report, dict) or report.get("need_id") != draft["need_id"]:
        raise ValueError("review must address the current need_id")
    decision = choice(report, "decision", ("accept", "revise"))
    coverage = choice(report, "coverage", COVERAGE)
    checks = report.get("checks")
    if not isinstance(checks, dict) or checks.keys() != set(CHECKS):
        raise ValueError("review must address direction, target_conditions, dependencies and content")
    checked = {key: choice(checks, key, ("pass", "gap", "error", "not_applicable")) for key in CHECKS}
    passages = tuple(string_leaves([draft, shared]))
    findings = []
    for row in rows(report, "findings"):
        quote = text(row, "quote")
        if not any(quote in passage for passage in passages):
            raise ValueError("each finding must quote actual candidate text")
        findings.append({"quote": quote, "request": text(row, "request"),
                         "source_ids": source_ids(row, "source_ids", tools.sources | tools.references)})
    if decision == "revise" and not findings:
        raise ValueError("revision requires a finding that quotes the candidate")
    if decision == "accept" and (findings or "error" in checked.values() or coverage != draft["coverage"]):
        raise ValueError("acceptance requires matching coverage and no unresolved review findings or errors")
    return {"need_id": draft["need_id"], "decision": decision, "coverage": coverage,
            "checks": checked, "findings": findings, "reason": text(report, "reason"),
            "upstream_questions": strings(report, "upstream_questions")}


def commit_items(draft, known):
    """Use exact content identities and already reviewed shared IDs."""
    local = {item["id"]: item for item in draft["items"]}
    mapped = {}
    committed = {}

    def resolve(ident):
        if ident in known:
            return ident
        if ident in mapped:
            return mapped[ident]
        row = local[ident]
        dependencies = sorted({resolve(dependency) for dependency in row["depends_on"]})
        core = {**{key: row[key] for key in ("kind", "title", "body")},
                "depends_on": dependencies, "source_ids": sorted(row["source_ids"])}
        item_id = "item:" + digest(core)
        mapped[ident] = item_id
        if item_id not in known:
            committed[item_id] = {"id": item_id, **core}
        return item_id

    uses = list(dict.fromkeys(resolve(ident) for ident in draft["item_ids"]))
    return committed, uses


def summarize(state):
    uses = state["uses"]
    states = Counter(row["status"] for row in uses.values())
    coverage = Counter(row["coverage"] for row in uses.values() if row["status"] == "accepted")
    attempts = [attempt for row in uses.values() for attempt in [*row.get("previous_attempts", []), row]]
    return {
        "total_needs": len(state["needs"]), "pending": len(state["needs"]) - len(uses),
        "blocked_functions": len(state["blocked_functions"]), "by_status": dict(states),
        "accepted_coverage": dict(coverage), "shared_items": len(state["items"]),
        "model_requests": sum(row["usage"]["model_requests"] for row in attempts),
        "reference_read_chars": sum(row["usage"]["reference_read_chars"] for row in attempts),
    }

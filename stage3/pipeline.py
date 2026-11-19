"""Production Stage 3 orchestration and durable per-need checkpoints."""

from dataclasses import asdict
import fcntl
import json
import math
import os
from pathlib import Path

from stage2.codex_backend import BackendError
from stage2.materials import MaterialReadError
from stage2.pipeline import save
from stage2.schedule import digest

from .exchange import (
    ExchangeLimit, Limits, NeedBudget, REVIEWER, ReadTools, TOOLS, WRITER,
    encode, exchange, source_for_model,
)
from .export import write_markdown
from .reports import commit_items, summarize, validate_draft, validate_review


SCHEMA_VERSION = 2
PIPELINE_VERSION = 1


def reader(role, index, evidence, items, budget):
    trace = {"role": role, "model_requests": 0, "actions": [],
             "delivered": [], "target_read_chars": 0, "reference_read_chars": 0,
             "protocol_errors": []}
    budget.trace.append(trace)
    return ReadTools(index, evidence, items, budget, trace)


def scope_of_search(trace):
    discovery = {"list_files", "search_references", "list_entries", "related_entries"}
    return [row for row in trace["actions"] if row["action"]["tool"] in discovery]


def relevant_sources(report, available):
    ids = set(report["evidence_ids"]) | {row["entry_id"] for row in report["references"]}
    return {key: value for key, value in available.items() if key in ids}


def stash_review_sources(report, available, retained):
    for finding in report["findings"]:
        for ident in finding["source_ids"]:
            retained[ident] = available[ident]


def prepare_packet(packet, need, reference_inventory, items, limits):
    material = {key: value for key, value in packet.items() if key not in ("need", "sources")}
    material["reuse_contracts"] = {
        ident: {**row, "branches": [source_for_model(entry) | {"text": None}
                                   for entry in row["branches"]]}
        for ident, row in packet.get("reuse_contracts", {}).items()
    }
    sources = packet.get("sources", [])
    context = {
        "calls": {row["call_id"]: row for row in material.get("calls", [])},
        "reuse_contracts": material["reuse_contracts"],
        "related_functions": material.get("related_functions", {}),
        "target_sources": {source["id"]: source for source in sources},
    }
    data = {"need": {key: value for key, value in need.items() if key != "calls"},
            "target_material": material, "target_sources": [source_for_model(source) for source in sources],
            "reference_inventory": {key: value for key, value in reference_inventory.items() if key != "files"},
            "existing_shared_items": len(items),
            "available_context": {category: len(rows) for category, rows in context.items()}}
    target_limit = min(28_000, limits.context_chars // 3)
    if len(encode(data)) <= target_limit:
        return data, sources, context

    for key in ("calls", "reuse_contracts", "related_functions"):
        material.pop(key, None)
    available = list(context["target_sources"].values())
    original_citations = {(row["path"], row["start"], row["end"])
                          for row in need["original"].get("evidence", [])}
    available.sort(key=lambda source: (
        source["kind"] != "function_source",
        (source["path"], source["start_line"], source["end_line"]) not in original_citations,
    ))
    initial = []
    data["target_sources"] = []
    for source in available:
        card = source_for_model(source)
        if len(encode(data)) + 2 * len(encode(card)) < target_limit:
            data["target_sources"].append(card)
            initial.append(source)
    return data, initial, context


def run_need(need, index, evidence, items, make_model, limits):
    budget = NeedBudget(limits)
    packet = evidence.for_need(need["id"], index)
    budget.read_errors.extend(packet.get("read_errors", []))
    data, base_sources, context = prepare_packet(packet, need, index.list_files(limit=1), items, limits)
    base_ids = {source["id"] for source in base_sources}
    history = []
    retained = {}
    draft = None
    audit = None
    search = []
    prior_sources = {}
    failure = None
    try:
        for attempt in range(limits.max_revisions + 1):
            writing = reader("write", index, evidence, items, budget)
            writing.context = context
            for source in base_sources:
                writing.deliver(source, evidence=True)
            writing.trace["prior_search_scope"] = search
            if prior_sources:
                for source, is_target in prior_sources.values():
                    if is_target and source["id"] not in writing.sources:
                        writing.deliver(source, evidence=True)
                    elif not is_target:
                        writing.forward_reference(source)
            draft, shared = exchange(
                make_model("write", need["id"]), "writer", WRITER, data, writing,
                lambda report, tools: validate_draft(report, tools, need),
            )
            audit = None
            collected = relevant_sources(draft, writing.sources | writing.references)
            retained.update(collected)
            search = [*search, *scope_of_search(writing.trace)]
            review_data = {key: value for key, value in data.items() if key != "previous_review"}
            followup = [source for source in collected.values() if source["id"] not in base_ids]
            call_records = [context["calls"][ident] for ident in draft["call_ids"]]
            review_data.update(candidate=draft, used_shared_items=shared,
                               cited_sources=[source_for_model(source) for source in followup],
                               candidate_call_records=call_records, writer_search_scope=search)
            reviewing = reader("review", index, evidence, items, budget)
            reviewing.context = context
            for source in base_sources:
                reviewing.deliver(source, evidence=True)
            for source in followup:
                if source["id"] in writing.sources:
                    reviewing.deliver(source, evidence=True)
                else:
                    reviewing.forward_reference(source)
            audit = exchange(
                make_model("review", need["id"]), "reviewer", REVIEWER, review_data, reviewing,
                lambda report, tools: validate_review(report, tools, draft, shared),
            )
            stash_review_sources(audit, reviewing.sources | reviewing.references, retained)
            history.append({"attempt": attempt + 1, "draft": draft, "review": audit,
                            "search_scope": search})
            if audit["decision"] == "accept":
                break
            supporting = dict(collected)
            stash_review_sources(audit, reviewing.sources | reviewing.references, supporting)
            prior_sources = {
                ident: (source, ident in reviewing.sources)
                for ident, source in supporting.items()
            }
            data["previous_review"] = {
                "candidate": draft, "used_shared_items": shared, "review": audit,
                "cited_sources": [source_for_model(source) for source, _ in prior_sources.values()
                                  if source["id"] not in base_ids],
                "search_scope": search,
            }
    except (BackendError, ExchangeLimit) as exc:
        failure = {"reason": str(exc), "type": type(exc).__name__}
        if getattr(exc, "details", None):
            failure["details"] = exc.details

    retryable_read = any(row.get("retryable") and not row.get("resolved")
                         for row in budget.read_errors)
    if failure or retryable_read:
        status = "retryable"
    elif audit and audit["decision"] == "accept":
        status = "accepted"
    else:
        status = "needs_review"

    if draft is None:
        committed, item_ids = {}, []
    elif status == "accepted":
        committed, item_ids = commit_items(draft, items)
    else:
        committed, item_ids = {}, []

    if need["status"] == "blocked" or need.get("conflicting_call_ids"):
        applicability = "blocked_upstream"
    elif need["status"] != "approved" or need["unverified_dependencies"]:
        applicability = "conditional_upstream"
    else:
        applicability = "requires_target_validation"

    row = {"need_id": need["id"], "function_id": need["function_id"], "status": status,
           "target_validation": "not_run", "applicability": applicability,
           "item_ids": item_ids, "review": audit, "usage": budget.summary(), "attempts": history}
    if draft is not None:
        for key in ("coverage", "disposition", "scope", "call_ids", "object_mapping", "conditions",
                    "remaining", "references"):
            row[key] = draft[key]
        row["evidence"] = [{key: retained[ident][key] for key in
                           ("id", "path", "start_line", "end_line", "file_sha256")}
                          for ident in draft["evidence_ids"]]
        row["search"] = {**draft["search"], "scope": search}
        if status != "accepted":
            row["uncommitted_draft"] = draft
    else:
        row.update(coverage="uncovered", disposition="gap", evidence=[], references=[],
                   remaining=["生成任务尚未产出通过格式检查的候选。"])
        row["search"] = {"status": "incomplete", "reason": "本轮尚无经过格式检查的检索判断。",
                         "scope": [entry for trace in budget.trace if trace["role"] == "write"
                                   for entry in scope_of_search(trace)]}
    if failure:
        row["failure"] = failure
    return row, committed, retained


def refresh(state):
    summary = summarize(state)
    if any(row["status"] != "accepted" for row in state["uses"].values()):
        status = "partial"
    elif summary["pending"]:
        status = "in_progress"
    elif state["blocked_functions"]:
        status = "partial"
    else:
        status = "completed"
    state.update(status=status, summary=summary)


def verify_committed_evidence(state, evidence):
    pinned = {}
    accepted = [row for row in state["uses"].values() if row["status"] == "accepted"]
    if accepted:
        for source in evidence.source_catalog.values():
            if source["kind"] == "compile_commands":
                pinned[source["path"]] = source["file_sha256"]
    for use in accepted:
        for exchange_data in use["usage"]["exchanges"]:
            for receipt in exchange_data["delivered"]:
                if "library_id" not in receipt and receipt.get("file_sha256"):
                    path, sha = receipt["path"], receipt["file_sha256"]
                    if pinned.setdefault(path, sha) != sha:
                        raise ValueError(f"resume found contradictory evidence digests for {path}")
    try:
        evidence.verify_files(pinned)
    except MaterialReadError as exc:
        raise ValueError(f"resume cannot reuse committed evidence: {exc}. Restore the pinned files to continue.") from exc


def check_limits(limits, max_needs):
    if (not math.isfinite(limits.timeout) or limits.timeout <= 0 or limits.context_chars < 12_000
            or limits.max_requests < 2 or limits.max_reads < 0 or limits.max_files < 0
            or limits.max_read_chars < 0 or limits.max_revisions < 0
            or (max_needs is not None and max_needs < 1)):
        raise ValueError("invalid stage-three timeout, budget or need-limit settings")


def run(*, stage2_result, output, model_factory, reference_manifest=None, stage1_result=None,
        top_level_spec=None, background=(), resume=False, need_ids=(), max_needs=None,
        limits=None, model_identity=None, progress=None):
    """Run pending needs and save stable shared items, use conditions and audit evidence."""
    from .evidence import load_evidence
    from .index import build_index

    limits = limits or Limits()
    check_limits(limits, max_needs)
    evidence = load_evidence(stage2_result, stage1_result=stage1_result,
                             top_level_spec=top_level_spec, background=background)
    index = build_index(reference_manifest if reference_manifest is not None else {"libraries": []})
    selection = list(dict.fromkeys(need_ids))
    unknown = set(selection).difference(evidence.needs)
    if unknown:
        raise ValueError(f"unknown need IDs: {', '.join(sorted(unknown))}")
    settings = asdict(limits)
    settings.pop("timeout")
    identity = json.loads(json.dumps({
        "pipeline_version": PIPELINE_VERSION, "evidence": evidence.identity,
        "references": index.identity, "prompt_sha256": digest([WRITER, REVIEWER, TOOLS]),
        "model": model_identity, "processing_settings": settings,
    }, ensure_ascii=False))
    output = Path(output).resolve()
    if not resume:
        output.mkdir(parents=True, exist_ok=False)
    handle = os.open(output, os.O_RDONLY | os.O_DIRECTORY)
    try:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise ValueError("another stage-three process is writing this run") from exc
        path = output / "stage3.json"
        markdown = output / "stage3.md"
        if resume:
            state = json.loads(path.read_text(encoding="utf-8"))
            if state.get("schema_version") != SCHEMA_VERSION or state.get("identity") != identity:
                raise ValueError("resume inputs or processing settings changed")
            verify_committed_evidence(state, evidence)
        else:
            state = {"schema_version": SCHEMA_VERSION, "mode": "production",
                     "identity": identity, "needs": evidence.needs,
                     "blocked_functions": evidence.blocked_functions,
                     "items": {}, "uses": {}, "sources": {}}
            refresh(state)
            save(path, state)
        pending = [ident for ident in (selection or state["needs"])
                   if ident not in state["uses"] or state["uses"][ident]["status"] == "retryable"]
        for ident in pending[:max_needs]:
            need = state["needs"][ident]
            if progress:
                progress(ident, "started")
            row, items, sources = run_need(need, index, evidence, state["items"], model_factory, limits)
            previous = state["uses"].get(ident)
            if previous:
                row["previous_attempts"] = [*previous.get("previous_attempts", []),
                                            {key: value for key, value in previous.items()
                                             if key != "previous_attempts"}]
            state["items"].update(items)
            state["sources"].update(sources)
            state["uses"][ident] = row
            refresh(state)
            save(path, state)
            if progress:
                progress(ident, row["status"])
        write_markdown(markdown, state)
        return state
    finally:
        os.close(handle)

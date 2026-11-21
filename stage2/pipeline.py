"""Stage two: generate contracts and atomically checkpoint completed tasks."""
import fcntl
import json
import math
import os
from pathlib import Path
from .storage import save
from .contract_store import ContractStore, DEFAULT_ROOT
from .contract_tools import ContractLog, ContractTools, DECISION_GUIDE, WRITE_GUIDE

from stage1.inputs import sha256
from .exchange import (ExchangeLimit, REVIEWER, TOOLS, WRITER, exchange,
                       validate_draft, validate_review)
from .materials import Materials, MaterialReadError
from .member_batches import (batch_task, member_keys, member_order, peer_check_evidence,
                             restore_checks, same_component_call)
from .schedule import digest, plan, task_description

GUIDE = Path(__file__).resolve().parents[1] / "SPECIFICATION_WRITING_GUIDE.md"


def evidence_payload(task, materials, reader, nodes):
    sources = {ident: materials.context_source(nodes[ident], reader) for ident in task["members"]}
    contracts = {}
    for call in task["outgoing"].values():
        callee = call["callee"]
        contract = materials.contracts.get(callee)
        if call["kind"] == "reuse" and contract and callee not in contracts:
            contracts[callee] = reader.excerpt(**contract)
    source_context = []
    seen = set()
    for call in task["incoming"].values():
        loc = call["location"]
        path, line = loc.get("path"), loc.get("line")
        if path in materials.paths and type(line) is int and line > 0 and (path, line) not in seen:
            seen.add((path, line))
            lines, _ = reader.lines(path)
            source_context.append(reader.excerpt(path, max(1, line - 2), min(len(lines), line + 2)))
    compilation = {}
    for ident, node in task["functions"].items():
        for unit in node.get("translation_units", []):
            alias = materials.alias(unit["library"], unit["path"])
            if alias in materials.compile_args:
                compilation[alias] = materials.compile_args[alias]
    return {"task": task, "source": sources, "caller_context": source_context,
            "configuration": materials.configuration, "compile_arguments": compilation,
            "reuse_contracts": contracts, "reference_paths": materials.reference_paths,
            "background_paths": materials.background}


def audit_calls(task, drafts, materials):
    members = set(task["members"])
    component = set(task.get("component_members", ()))
    peers = task.get("peer_contracts", {})
    audit = {}
    for key, call in {**task["outgoing"], **task["incoming"]}.items():
        caller, callee = call["caller"], call["callee"]
        recursive = same_component_call(call, component)
        upstream = peers.get(caller) if recursive else task["upstream"].get(caller)
        if caller in members:
            requirements = drafts[caller]["call_requirements"]
        else:
            requirements = upstream["call_requirements"] if upstream else []
        requirement = next((r for r in requirements if r["call_id"] == key), None)
        if call["kind"] == "internal" and callee not in members and not recursive:
            continue  # Evaluated with the later callee task.
        complete = requirement is not None and (
            (call["kind"] == "internal" and (not recursive or callee in members or callee in peers)) or
            (call["kind"] == "reuse" and callee in materials.contracts)
        )
        audit[key] = {"call": call, "requirement": requirement, "incomplete": not complete}
    return audit


def review_results(task, drafts, reviews, checks, audit):
    output = {}
    for ident, row in reviews.items():
        relevant = {key: check for key, check in checks.items()
                    if ident in (audit[key]["call"]["caller"], audit[key]["call"]["callee"])}
        status = row["status"]
        reasons = []
        for key, check in relevant.items():
            if check["status"] == "conflict":
                status = "blocked"
                reasons.append(key)
            elif check["status"] == "unknown":
                if status == "approved":
                    status = "conditional"
                reasons.append(key)
        for parent, upstream in task["upstream"].items():
            if upstream and upstream["status"] == "approved":
                continue
            if any(item["caller"] == parent and item["callee"] == ident
                   for item in task["incoming"].values()):
                if status == "approved":
                    status = "conditional"
                reasons.append(f"upstream: {parent}")
        if task["functions"][ident]["status"] == "syntax_fallback" and status == "approved":
            status = "conditional"
            reasons.append("source analysis used syntax fallback")
        summary = {"status": status, "reason": row["reason"], "unverified_dependencies": reasons}
        output[ident] = {**summary, "draft": drafts[ident], "call_checks": relevant}
    return output


def revision_task(task, members, drafts):
    """Restrict writable functions, with unchanged neighbours available for call checks."""
    selected = set(members)
    outgoing = {k: c for k, c in task["outgoing"].items() if c["caller"] in selected}
    incoming = {k: c for k, c in task["incoming"].items() if c["callee"] in selected}
    neighbours = {c["callee"] for c in outgoing.values()} | {c["caller"] for c in incoming.values()}
    peers = {ident: data for ident, data in task.get("peer_contracts", {}).items() if ident in neighbours}
    for ident in neighbours.intersection(drafts) - selected:
        draft = drafts[ident]
        peers[ident] = {k: draft[k] for k in ("symbols", "cases", "assumptions")}
        peers[ident]["call_requirements"] = [row for row in draft["call_requirements"]
                                             if row["call_id"] in incoming]
    return {**task, "members": members, "functions": {k: task["functions"][k] for k in members},
            "outgoing": outgoing, "incoming": incoming, "peer_contracts": peers}


def reviewed_round(task, writable, previous, findings, nodes, materials, factory, guide, timeout, max_chars):
    writer = materials.reader()
    data = evidence_payload(writable, materials, writer, nodes)
    if findings is not None:
        data["previous_drafts"] = {k: previous[k] for k in writable["members"]}
        data["previous_review"] = findings
        data["revision_instructions"] = (
            "Revise only task.members using their previous drafts and review findings. "
            "Use peer_contracts as read-only context. Read cited source again when needed.")
    data["writing_guide"] = str(GUIDE)
    ident = ",".join(writable["members"])
    tools = ContractTools(writable, nodes, materials) if materials.contract_log else None
    has_builtins = tools and bool(tools.calls)
    if has_builtins:
        data["builtin_calls"] = tools.calls
        # Reopen a proposal left pending by an interrupted run of this task.
        history = [p for p in tools.log.data["events"] if p["calls"].keys() <= tools.calls.keys()]
        tools.proposals = {p["proposal_id"]: p for p in history if p["status"] == "pending"}
        if history and history[-1]["status"] in ("rejected", "stale"):
            data["contract_change_feedback"] = [tools.feedback(history[-1])]

    def finish_writer(report, reader):
        if has_builtins:
            tools.require_lookups()
        return validate_draft(report, reader, writable, nodes, digest)

    for attempt in range(3):
        if has_builtins:
            tools.attach(writer, "write" if attempt < 2 else "lookup")
            tools.looked_up.clear()
        edits, proposals = exchange(
            factory("write", ident), WRITER, {"guide": guide + ("\n" + WRITE_GUIDE if has_builtins else ""),
                                              "data": data}, writer, finish_writer,
            timeout=timeout, max_chars=max_chars,
        )
        if not has_builtins or not tools.proposals:
            break
        pending = [p for p in tools.proposals.values() if p["status"] == "pending"]
        if pending:
            inspector = materials.reader()
            tools.attach(inspector, "contract_review")
            exchange(factory("review", ident), DECISION_GUIDE,
                     {"guide": "", "data": {"proposals": pending, "source": data["source"],
                                            "background_paths": materials.background}},
                     inspector, tools.finish_decisions, timeout=timeout, max_chars=max_chars)
        data["contract_change_feedback"] = [tools.feedback(p) for p in tools.proposals.values()]
        tools.proposals = {}
        writer = materials.reader()
        # Keep all pre-delivered source/background ranges in the fresh writer's citation ledger.
        data.update(evidence_payload(writable, materials, writer, nodes))
        if attempt == 1:
            data["contract_change_limit"] = "Use approved rules or leave unknown on this pass."
    drafts = {**previous, **edits}
    # Accepted edges carry the observed source proof forward, even if this
    # draft will be refreshed after the new scope takes effect.
    known = {(row["caller"], row["callee"], row["location"].get("path"),
              row["location"].get("line"), row["location"].get("column"))
             for row in task["outgoing"].values()}
    proposals = {
        key: proposal for key, proposal in proposals.items()
        if tuple(proposal[k] for k in ("caller", "callee", "path", "line", "column")) not in known
    }
    reviewer = materials.reader()
    audit = audit_calls(task, drafts, materials)
    affected = {k: row for k, row in audit.items()
                if k in writable["outgoing"] or k in writable["incoming"]}
    review_data = evidence_payload(writable, materials, reviewer, nodes)
    builtin_refs = {}
    if has_builtins:
        rules = {}
        for key, hit in tools.looked_up.items():
            if hit["status"] != "matched" or key not in affected:
                continue
            ref = {k: hit[k] for k in ("id", "version", "digest")}
            ref.update(operation=tools.calls[key]["name"], profile=tools.calls[key]["profile"])
            builtin_refs[key] = ref
            affected[key]["contract"] = ref
            affected[key]["incomplete"] = affected[key]["requirement"] is None
            rules[hit["digest"]] = hit["spec"]
        reviewer.contract_actions = {"lookup_contract": tools.lookup_pinned}
        review_data["builtin_contracts"] = rules
        review_data["builtin_audit_instructions"] = (
            "lookup_contract(call_id or call_ids) returns the pinned writer lookup. "
            "Audit source use against the exact contract referenced by each call; matching a rule "
            "alone is insufficient. Check operands and lifecycle on each relevant path. Use conflict "
            "for a demonstrated violation, unknown for missing evidence.")
    cited = {}
    for record in [*edits.values(), *proposals.values(),
                   *(need for draft in edits.values() for need in draft["common_needs"])]:
        for ref in record["evidence"]:
            key = (ref["path"], ref["start"], ref["end"])
            if key not in cited:
                cited[key] = reviewer.excerpt(*key)
    review_data.update(writing_guide=str(GUIDE), drafts=edits, edge_proposals=proposals, audit_calls=affected,
                       cited_sources=list(cited.values()))
    if "component_members" in task:
        review_data["component_audit_instructions"] = (
            "Review only the functions in task.members. For recursive calls between batches, compare the "
            "current drafts with the independently reviewed task.peer_contracts, using the caller's "
            "call requirement and the callee's cases. Source may be requested by its listed interval. "
            "Mark calls with incomplete evidence unknown. A pending peer alone does not reduce the "
            "function's own source review status. The pipeline separately records pending call checks.")
    if findings is not None:
        review_data["revision_instructions"] = (
            "Review the revised drafts and recheck their incoming and outgoing calls. "
            "The unchanged neighbours' contracts in task.peer_contracts are read-only.")
    reviews, checks, decisions = exchange(
        factory("review", ident), REVIEWER, {"guide": guide, "data": review_data}, reviewer,
        lambda report, _: validate_review(report, writable, affected, proposals),
        timeout=timeout, max_chars=max_chars,
    )
    if has_builtins:
        for key, hit in tools.looked_up.items():
            if key in checks:
                checks[key]["contract_lookup"] = hit["status"]
                if key in builtin_refs:
                    checks[key]["contract"] = builtin_refs[key]
    accepted = {key: {**proposals[key], "review_reason": row["reason"]}
                for key, row in decisions.items() if row["accept"]}
    return drafts, reviews, checks, audit, accepted


def run_task(task, nodes, materials, factory, guide, timeout, max_chars, max_revisions):
    drafts, reviews, checks = {}, {}, {}
    remaining = dict.fromkeys(task["members"], max_revisions)
    writable, findings = task, None
    while True:
        try:
            drafts, updated_reviews, updated_checks, audit, accepted = reviewed_round(
                task, writable, drafts, findings, nodes, materials, factory, guide, timeout, max_chars)
        except (ExchangeLimit, MaterialReadError) as exc:
            if findings is None:
                raise
            for ident in writable["members"]:
                output[ident]["revision_error"] = str(exc)
            return output, {}
        reviews.update(updated_reviews)
        checks.update(updated_checks)
        output = review_results(task, drafts, reviews, checks, audit)
        if "component_members" in task:
            component = set(task["component_members"])
            standalone = {key: check for key, check in checks.items()
                          if not same_component_call(audit[key]["call"], component)}
            base = review_results(task, drafts, reviews, standalone, audit)
            evidence = peer_check_evidence(task, drafts, audit, checks)
            for ident, row in output.items():
                row["member_review"] = {key: base[ident][key] for key in
                                        ("status", "unverified_dependencies", "call_checks")}
                row["member_review"]["peer_checks"] = {key: item for key, item in evidence.items()
                                                       if ident in item["drafts"]}
        if accepted:
            return output, accepted
        # Fix explicit function findings first. A shared conflicting call can
        # block both endpoints even when only one function needs a textual edit.
        rejected = {k for k, row in reviews.items() if row["status"] == "blocked"}
        to_revise = set(rejected)
        for key, check in checks.items():
            if check["status"] == "conflict":
                call = audit[key]["call"]
                endpoints = {call["caller"], call["callee"]}.intersection(reviews)
                if not endpoints.intersection(rejected):
                    to_revise.update(endpoints)
        pending = [k for k in task["members"] if k in to_revise and remaining[k]]
        if not pending:
            return output, {}
        writable = revision_task(task, pending, drafts)
        for k in pending:
            remaining[k] -= 1
        findings = {"functions": {k: reviews[k] for k in pending},
                    "call_checks": {k: row for k, row in checks.items()
                                    if k in writable["outgoing"] or k in writable["incoming"]}}


def reconcile(stage1, state, materials, planned, *, stop_after_functions=None):
    scope, nodes, calls, outgoing, incoming, deps = planned
    kept, next_task = {}, None
    batch_size = state.get("member_batch_size")
    for component in scope["components"]:
        members = component["functions"]
        task = task_description(members, nodes, outgoing, incoming, deps, kept)
        key = digest(task)
        existing = [state["functions"].get(ident) for ident in members]
        if all(row and row["task_digest"] == key for row in existing):
            kept.update(zip(members, existing))
        elif batch_size and len(members) > 1:
            keys = member_keys(members, nodes, outgoing, incoming, deps, kept)
            kept.update({ident: row for ident, row in zip(members, existing)
                         if row and "member_review" in row and row["task_digest"] == keys[ident]})
            restore_checks(set(members), kept, calls)
            remaining = set(members) - kept.keys()
            if remaining and next_task is None:
                order = member_order(members, nodes, outgoing, incoming, deps)
                next_task = [ident for ident in order if ident in remaining], members, keys
        elif next_task is None:
            next_task = task, key

    state["functions"] = kept
    state["scope"] = scope
    state["calls"] = calls
    citations = {ref["path"] for edge in state["accepted_edges"].values() for ref in edge["evidence"]}
    for record in kept.values():
        draft = record.get("draft")
        if draft:
            citations.update(ref["path"] for ref in draft["evidence"])
            citations.update(ref["path"] for need in draft["common_needs"] for ref in need["evidence"])
    citations.update(contract["path"] for contract in materials.contracts.values())
    state["external_materials"] = {
        alias: {"path": str(materials.paths[alias]), "sha256": materials.digests[alias]}
        for alias in sorted(citations) if not alias.startswith("project/")
    }
    selected = set(scope["reached_ids"])
    resolved = {digest(call["detail"]["resolved_stage1_gap"]) for call in calls.values()
                if "resolved_stage1_gap" in call.get("detail", {})}
    state["analysis_gaps"] = [gap for gap in stage1["graph"]["analysis_gaps"]
                              if gap["caller"] in selected and (not resolved or digest(gap) not in resolved)]
    state["analysis_translation_failures"] = [
        unit for unit in stage1["coverage"]["translation_units"] if unit["status"] != "parsed"
    ]
    if next_task:
        state["status"] = "in_progress"
    else:
        partial = (state["analysis_gaps"] or state["analysis_translation_failures"]
                   or any(function["status"] != "approved" for function in kept.values())
                   or any(check["status"] != "compatible" for function in kept.values()
                          for check in function["call_checks"].values()))
        state["status"] = "partial" if partial else "completed"
    if next_task and len(next_task) == 3:
        pending, members, keys = next_task
        limit = batch_size
        if stop_after_functions is not None:
            limit = max(0, min(limit, stop_after_functions - len(kept)))
        batch = pending[:limit]
        if batch:
            return batch_task(batch, members, nodes, outgoing, incoming, deps, kept, materials), keys
        return None
    return next_task


def run(*, stage1_result, output, model_factory, background=(), reuse_contracts=None, resume=False,
        timeout=600, max_chars=100_000, max_revisions=1, model_identity=None,
        member_batch_size=None, stop_after_functions=None, contract_store_root=DEFAULT_ROOT):
    """Read stage one, generate contracts, and return the stage-two JSON handoff."""
    if not math.isfinite(timeout) or timeout <= 0 or max_chars < 30_000 or max_revisions < 0:
        raise ValueError("expected positive timeout, at least 30000 context characters, and nonnegative revisions")
    if (member_batch_size is not None and member_batch_size < 1
            or stop_after_functions is not None and stop_after_functions < 1):
        raise ValueError("member batch size and function limit must be positive")
    stage1_path = Path(stage1_result).resolve(strict=True)
    stage1 = json.loads(stage1_path.read_text(encoding="utf-8"))
    if stage1.get("schema_version") != 1 or stage1.get("status") not in ("analysis_completed", "partial_analysis"):
        raise ValueError("expected a completed or partial stage-one result with schema_version 1")
    output = Path(output).resolve()
    if output.is_relative_to(stage1_path.parent):
        raise ValueError("output must be outside the stage-one run")
    materials = Materials(stage1_path, stage1, background, reuse_contracts, output)
    materials.configuration = stage1["configuration"]
    guide = GUIDE.read_text(encoding="utf-8")
    identity = {
        "stage1_sha256": sha256(stage1_path), "writing_guide_sha256": sha256(GUIDE),
        "materials_sha256": digest(materials.digests), "reuse_contracts": materials.contracts,
        "prompt_sha256": digest([WRITER, REVIEWER, TOOLS]), "model": model_identity,
        "max_chars": max_chars, "max_revisions": max_revisions,
    }
    if not resume:
        output.mkdir(parents=True, exist_ok=False)
    handle = os.open(output, os.O_RDONLY | os.O_DIRECTORY)
    try:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise ValueError("another stage-two process is writing this run") from exc
        path = output / "stage2.json"
        if resume:
            state = json.loads(path.read_text(encoding="utf-8"))
            if state.get("schema_version") != 1 or state["identity"] != identity:
                raise ValueError("resume input or task settings changed")
            state["stage1_result"] = str(stage1_path)
        else:
            state = {"schema_version": 1, "identity": identity, "stage1_result": str(stage1_path),
                     "functions": {}, "accepted_edges": {}, "formal_call_validation": "not_run"}
        store = ContractStore(Path(contract_store_root).resolve())
        stored_root = state.setdefault("contract_store", str(store.root))
        if stored_root != str(store.root):
            raise ValueError("resume contract store changed")
        materials.contract_log = ContractLog(output, store)
        state["contract_changes"] = materials.contract_log.path.name
        if member_batch_size is not None:
            state["member_batch_size"] = member_batch_size
        elif stop_after_functions is not None:
            state.setdefault("member_batch_size", 1)
        planned = plan(stage1, state["accepted_edges"], materials)
        next_task = reconcile(stage1, state, materials, planned, stop_after_functions=stop_after_functions)
        save(path, state)
        while next_task and (stop_after_functions is None or len(state["functions"]) < stop_after_functions):
            task, key = next_task
            try:
                records, accepted = run_task(task, planned[1], materials, model_factory, guide,
                                             timeout, max_chars, max_revisions)
            except (ExchangeLimit, MaterialReadError) as exc:
                if "component_members" in task:
                    raise
                records = {ident: {"status": "blocked", "reason": str(exc), "draft": None,
                                  "call_checks": {}} for ident in task["members"]}
                accepted = {}
            for ident, record in records.items():
                task_digest = key[ident] if isinstance(key, dict) else key
                state["functions"][ident] = {**record, "task_digest": task_digest}
            new = accepted.keys() - state["accepted_edges"].keys()
            if new:
                state["accepted_edges"].update({key: accepted[key] for key in new})
                planned = plan(stage1, state["accepted_edges"], materials)
            next_task = reconcile(stage1, state, materials, planned, stop_after_functions=stop_after_functions)
            save(path, state)
        return state
    finally:
        os.close(handle)

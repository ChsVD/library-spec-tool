"""Stage two: generate contracts and atomically checkpoint completed tasks."""
import fcntl
import json
import math
import os
from pathlib import Path
from tempfile import NamedTemporaryFile

from stage1.inputs import sha256
from .exchange import (ExchangeLimit, REVIEWER, TOOLS, WRITER, exchange,
                       validate_draft, validate_review)
from .materials import Materials, MaterialReadError
from .schedule import digest, plan, task_description

GUIDE = Path(__file__).resolve().parents[1] / "SPECIFICATION_WRITING_GUIDE.md"


def save(path, state):
    with NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as stream:
        temp = Path(stream.name)
        try:
            json.dump(state, stream, ensure_ascii=False, indent=2)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
            os.replace(temp, path)
            directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(directory)
            finally:
                os.close(directory)
        finally:
            temp.unlink(missing_ok=True)


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
    audit = {}
    for key, call in {**task["outgoing"], **task["incoming"]}.items():
        caller, callee = call["caller"], call["callee"]
        upstream = task["upstream"].get(caller)
        if caller in members:
            requirements = drafts[caller]["call_requirements"]
        else:
            requirements = upstream["call_requirements"] if upstream else []
        requirement = next((r for r in requirements if r["call_id"] == key), None)
        if call["kind"] == "internal" and callee not in members:
            continue  # Evaluated with the later callee task.
        complete = requirement is not None and (
            call["kind"] == "internal" or
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
            elif check["status"] == "unknown" and status == "approved":
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


def run_task(task, nodes, materials, factory, guide, timeout, max_chars, max_revisions):
    findings = None
    accepted = {}
    for revision in range(max_revisions + 1):
        writer = materials.reader()
        data = evidence_payload(task, materials, writer, nodes)
        if findings is not None:
            data["previous_review"] = findings
        data["writing_guide"] = str(GUIDE)
        ident = ",".join(task["members"])
        drafts, proposals = exchange(
            factory("write", ident), WRITER, {"guide": guide, "data": data}, writer,
            lambda report, reader: validate_draft(report, reader, task, nodes, digest),
            timeout=timeout, max_chars=max_chars,
        )
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
        review_data = evidence_payload(task, materials, reviewer, nodes)
        cited = {}
        for record in [*drafts.values(), *proposals.values(),
                       *(need for draft in drafts.values() for need in draft["common_needs"])]:
            for ref in record["evidence"]:
                key = (ref["path"], ref["start"], ref["end"])
                if key not in cited:
                    cited[key] = reviewer.excerpt(*key)
        review_data.update(writing_guide=str(GUIDE), drafts=drafts, edge_proposals=proposals, audit_calls=audit,
                           cited_sources=list(cited.values()))
        reviews, checks, decisions = exchange(
            factory("review", ident), REVIEWER, {"guide": guide, "data": review_data}, reviewer,
            lambda report, _: validate_review(report, task, audit, proposals),
            timeout=timeout, max_chars=max_chars,
        )
        accepted.update({key: {**proposals[key], "review_reason": row["reason"]}
                         for key, row in decisions.items() if row["accept"]})
        output = review_results(task, drafts, reviews, checks, audit)
        if accepted or all(record["status"] != "blocked" for record in output.values()):
            break
        findings = {"functions": reviews, "call_checks": checks}
    return output, accepted


def reconcile(stage1, state, materials, planned):
    scope, nodes, calls, outgoing, incoming, deps = planned
    kept, next_task = {}, None
    for component in scope["components"]:
        members = component["functions"]
        task = task_description(members, nodes, outgoing, incoming, deps, kept)
        key = digest(task)
        existing = [state["functions"].get(ident) for ident in members]
        if all(row and row["task_digest"] == key for row in existing):
            kept.update(zip(members, existing))
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
    state["analysis_gaps"] = [gap for gap in stage1["graph"]["analysis_gaps"] if gap["caller"] in selected]
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
    return next_task


def run(*, stage1_result, output, model_factory, background=(), reuse_contracts=None, resume=False,
        timeout=600, max_chars=100_000, max_revisions=1, model_identity=None):
    """Read stage one, generate contracts, and return the stage-two JSON handoff."""
    if not math.isfinite(timeout) or timeout <= 0 or max_chars < 30_000 or max_revisions < 0:
        raise ValueError("expected positive timeout, at least 30000 context characters, and nonnegative revisions")
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
        planned = plan(stage1, state["accepted_edges"], materials)
        next_task = reconcile(stage1, state, materials, planned)
        save(path, state)
        while next_task:
            task, key = next_task
            try:
                records, accepted = run_task(task, planned[1], materials, model_factory, guide,
                                             timeout, max_chars, max_revisions)
            except (ExchangeLimit, MaterialReadError) as exc:
                records = {ident: {"status": "blocked", "reason": str(exc), "draft": None,
                                  "call_checks": {}} for ident in task["members"]}
                accepted = {}
            for ident, record in records.items():
                state["functions"][ident] = {**record, "task_digest": key}
            new = accepted.keys() - state["accepted_edges"].keys()
            if new:
                state["accepted_edges"].update({key: accepted[key] for key in new})
                planned = plan(stage1, state["accepted_edges"], materials)
            next_task = reconcile(stage1, state, materials, planned)
            save(path, state)
        return state
    finally:
        os.close(handle)

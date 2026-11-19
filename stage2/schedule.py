"""Derive the current workload and call requirements from saved results."""
from collections import defaultdict
from copy import deepcopy
import hashlib
import json

from stage1.graph import compute_scope


def digest(value):
    data = json.dumps(value, ensure_ascii=False, sort_keys=True).encode()
    return hashlib.sha256(data).hexdigest()


def plan(stage1, proposals, materials):
    graph = deepcopy(stage1["graph"])
    nodes = graph["nodes"]
    if proposals:
        for ident, proposal in proposals.items():
            src = nodes[proposal["caller"]]["source"]
            graph["edges"]["stage2-" + ident] = {
                "caller": proposal["caller"], "callee": proposal["callee"],
                "callsites": [{"path": src["path"], "line": proposal["line"], "column": proposal["column"],
                               "kind": "indirect_candidate", "evidence": "stage2_review",
                               "proposal_id": ident}],
            }
        scope = compute_scope(graph, stage1["scope"]["entry_ids"])
    else:
        scope = stage1["scope"]

    selected = set(scope["function_ids"])
    reached = set(scope["reached_ids"])
    calls = {}
    outgoing, incoming = defaultdict(dict), defaultdict(dict)

    def add(caller, callee, location, kind, detail=None):
        if caller not in reached or (caller not in selected and callee not in selected):
            return
        if location.get("path") and location.get("line"):
            library = nodes[caller]["library"]
            location = {**location, "path": materials.alias(library, location["path"])}
        key = "call-" + digest([caller, callee, kind, location, detail])[:24]
        calls[key] = {"caller": caller, "callee": callee, "kind": kind, "location": location}
        if detail:
            calls[key]["detail"] = detail
        outgoing[caller][key] = calls[key]
        if callee:
            incoming[callee][key] = calls[key]

    for edge in graph["edges"].values():
        caller, callee = edge["caller"], edge["callee"]
        for site in edge["callsites"]:
            kind = "reuse" if nodes[callee]["library"] != "target" else "internal"
            loc = {k: site.get(k) for k in ("path", "line", "column")}
            extra = {"source_kind": site["kind"], "evidence": site["evidence"]}
            if "proposal_id" in site:
                extra["proposal"] = proposals[site["proposal_id"]]
            add(caller, callee, loc, kind, extra)
    for record in graph["external_calls"]:
        add(record["caller"], None, record["location"], "external", record)
    for record in graph["analysis_gaps"]:
        add(record["caller"], None, record["location"], "unresolved", record)
    # A reference-mediated callback may be known only as a scheduling dependency.
    # Keep its relation separate from real call sites.
    dependencies = defaultdict(set)
    for edge in scope.get("callback_dependencies", []):
        dependencies[edge["callee"]].add(edge["caller"])
    return scope, nodes, calls, outgoing, incoming, dependencies


def task_description(members, nodes, outgoing, incoming, dependencies, valid):
    outgoing_calls = {key: row for ident in members for key, row in outgoing[ident].items()}
    incoming_calls = {key: row for ident in members for key, row in incoming[ident].items()}
    parents = {row["caller"] for row in incoming_calls.values()} | set().union(
        *(dependencies[ident] for ident in members))
    upstream = {}
    for parent in sorted(parents - set(members)):
        result = valid.get(parent)
        usable = result and result["status"] in ("approved", "conditional")
        upstream[parent] = None
        if usable:
            draft = result["draft"]
            upstream[parent] = {k: draft[k] for k in ("cases", "assumptions")}
            upstream[parent]["status"] = result["status"]
            upstream[parent]["call_requirements"] = [
                requirement for requirement in draft["call_requirements"] if requirement["call_id"] in incoming_calls
            ]
    return {"members": sorted(members), "functions": {ident: nodes[ident] for ident in members},
            "outgoing": outgoing_calls, "incoming": incoming_calls, "upstream": upstream}

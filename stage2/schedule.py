"""Derive the current workload and call requirements from saved results."""
from collections import Counter, defaultdict
from copy import deepcopy
import hashlib
import json

from stage1.graph import compute_scope


def digest(value):
    data = json.dumps(value, ensure_ascii=False, sort_keys=True).encode()
    return hashlib.sha256(data).hexdigest()


def resolved_direct_calls(graph, proposals, materials):
    """Match reviewed target identities to individual named stage-one gaps."""
    if not proposals:
        return {}
    nodes = graph["nodes"]
    by_site = defaultdict(list)
    for ident, proposal in proposals.items():
        site = tuple(proposal[k] for k in ("caller", "path", "line", "column"))
        by_site[site].append(ident)

    def site_key(caller, loc):
        path = materials.alias(nodes[caller]["library"], loc["path"])
        return caller, path, loc["line"], loc.get("column")

    gaps = defaultdict(list)
    for gap in graph["analysis_gaps"]:
        key = site_key(gap["caller"], gap["location"])
        if key in by_site:
            gaps[key].append(gap)
    # A macro expansion can map several calls to one source position.
    competing = set()
    for edge in graph["edges"].values():
        for loc in edge["callsites"]:
            key = site_key(edge["caller"], loc)
            if key in gaps:
                competing.add(key)
    for call in graph["external_calls"]:
        competing.add(site_key(call["caller"], call["location"]))

    names = Counter(n["name"] for n in nodes.values())
    matched = {}
    for key, records in gaps.items():
        if key in competing or len(records) != 1 or len(by_site[key]) != 1 or not key[3]:
            continue
        gap = records[0]
        ident = by_site[key][0]
        proposal = proposals[ident]
        node = nodes[proposal["callee"]]
        if (gap["reason"] != "unconfirmed_call_target" or gap.get("name") != node["name"]
                or names[node["name"]] != 1 or node["status"] != "definition"
                or set(gap.get("candidate_ids", [])) - {proposal["callee"]}):
            continue
        source = node["source"]
        path = materials.alias(node["library"], source["path"])
        if node.get("linkage") == "internal" and path != key[1]:
            continue
        if any(ref["path"] == path and ref["start"] <= source["line"] <= ref["end"]
               for ref in proposal["evidence"]):
            matched[ident] = gap
    return matched


def plan(stage1, proposals, materials):
    graph = deepcopy(stage1["graph"])
    nodes = graph["nodes"]
    resolved = resolved_direct_calls(graph, proposals, materials)
    if proposals:
        for ident, proposal in proposals.items():
            src = nodes[proposal["caller"]]["source"]
            graph["edges"]["stage2-" + ident] = {
                "caller": proposal["caller"], "callee": proposal["callee"],
                "callsites": [{"path": src["path"], "line": proposal["line"], "column": proposal["column"],
                               "kind": "direct" if ident in resolved else "indirect_candidate", "evidence": "stage2_review",
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
                if site["proposal_id"] in resolved:
                    extra["resolved_stage1_gap"] = resolved[site["proposal_id"]]
            add(caller, callee, loc, kind, extra)
    for record in graph["external_calls"]:
        add(record["caller"], None, record["location"], "external", record)
    resolved_keys = {digest(gap) for gap in resolved.values()}
    for record in graph["analysis_gaps"]:
        if resolved_keys and digest(record) in resolved_keys:
            continue
        add(record["caller"], None, record["location"], "unresolved", record)
    # A reference-mediated callback may be known only as a scheduling dependency.
    # Keep its relation separate from real call sites.
    dependencies = defaultdict(set)
    for edge in scope.get("callback_dependencies", []):
        dependencies[edge["callee"]].add(edge["caller"])
    return scope, nodes, calls, outgoing, incoming, dependencies


def task_description(members, nodes, outgoing, incoming, dependencies, valid, *, peers=()):
    outgoing_calls = {key: row for ident in members for key, row in outgoing[ident].items()}
    incoming_calls = {key: row for ident in members for key, row in incoming[ident].items()}
    parents = {row["caller"] for row in incoming_calls.values()} | set().union(
        *(dependencies[ident] for ident in members))
    upstream = {}
    for parent in sorted(parents - set(members) - set(peers)):
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

"""Plan multi-target demand scopes from saved graphs; never rebuild or call models."""
import argparse
import copy
import json
from pathlib import Path
from stage1.runner import snapshot
from stage1.task import write_json, write_text
from .graph import digest, layers

VERSION = 2


def read_graph_run(root, source):
    source = Path(source).resolve(strict=True)
    graph = json.loads((source / "graph.json").read_text())
    identity = json.loads((source / "identity.json").read_text())
    status = json.loads((source / "status.json").read_text())
    if graph.get("status") != "unverified_reference_graph":
        raise ValueError("demand scope requires a reference graph")
    if status.get("graph_digest") != digest(graph) or (source / "input_changed.json").exists():
        raise ValueError("source graph/status changed or input marked stale")
    if snapshot(Path(root).resolve(strict=True)) != identity["input_snapshot"]:
        raise ValueError("input differs from source graph snapshot")
    for ident, node in graph["nodes"].items():
        if node.get("id") != ident:
            raise ValueError("invalid function identity")
    for ident, edge in graph["edges"].items():
        if edge.get("id") != ident or any(edge[k] not in graph["nodes"] for k in ("caller", "callee")):
            raise ValueError("invalid graph edge")
    return graph, identity


def _ids(values, nodes, name, required=False):
    if not isinstance(values, list) or (required and not values):
        raise ValueError(name + " must be a nonempty list" if required else name + " must be a list")
    if any(not isinstance(v, str) or v not in nodes for v in values) or len(set(values)) != len(values):
        raise ValueError(name + " must contain unique exact function IDs (not bare symbols)")
    return set(values)


def _plan_graph_v1(graph, target_ids, root_ids=None):
    """SCC-closed union of all ancestor paths, optionally bounded by explicit roots."""
    nodes = graph["nodes"]
    targets = _ids(target_ids, nodes, "target_ids", True)
    roots = _ids(root_ids, nodes, "root_ids", True) if root_ids is not None else None
    full = copy.deepcopy(graph)
    for n in full["nodes"].values():
        n["selected"] = True
    components = [g for layer in layers(full) for g in layer]
    owners = {n: set(c) for c in components for n in c}
    expanded_targets = set().union(*(owners[n] for n in targets))
    adj = {n: set() for n in nodes}; rev = {n: set() for n in nodes}
    for edge in graph["edges"].values():
        adj[edge["caller"]].add(edge["callee"]); rev[edge["callee"]].add(edge["caller"])
    def reach(seeds, links):
        visited = set(seeds); todo = list(seeds)
        while todo:
            for n in links[todo.pop()] - visited:
                visited.add(n); todo.append(n)
        return visited
    ancestors = reach(expanded_targets, rev)
    if roots is None:
        keep = ancestors
    else:
        expanded_roots = set().union(*(owners[n] for n in roots))
        if not expanded_roots <= ancestors:
            raise ValueError("each requested root must reach a target")
        descendants = reach(expanded_roots, adj)
        if not expanded_targets <= descendants:
            raise ValueError("every target SCC must be reachable from requested roots")
        keep = ancestors & descendants
    boundary = [e for e in graph["edges"].values() if (e["caller"] in keep) != (e["callee"] in keep)]
    context = {e["callee"] if e["caller"] in keep else e["caller"] for e in boundary}
    return {
        "version": 1, "kind": "multi-target-demand-scope",
        "requested_target_ids": sorted(targets), "target_ids": sorted(expanded_targets),
        "scc_added_target_ids": sorted(expanded_targets - targets),
        "root_ids": sorted(roots) if roots is not None else None,
        "policy": "all-ancestors" if roots is None else "all-paths-from-explicit-roots",
        "generation_ids": sorted(keep), "demand_ids": sorted(keep - expanded_targets),
        "context_ids": sorted(context),
        "boundary_edge_ids": sorted(e["id"] for e in boundary),
        "excluded_incoming_edge_ids": sorted(e["id"] for e in boundary if e["callee"] in keep),
        "outgoing_boundary_edge_ids": sorted(e["id"] for e in boundary if e["caller"] in keep),
        "excluded_ancestor_ids": sorted(ancestors - keep),
        "components": [c for c in components if set(c) <= keep],
        "unknown_call_count": sum(u.get("caller") in keep for u in graph.get("unknown_calls", [])),
        "inventory_gaps": copy.deepcopy(graph.get("inventory_gaps", [])),
        "coverage": "Only identified candidate paths in the saved graph; external/indirect/configuration gaps remain unknown",
    }



def plan_graph(graph, target_ids, root_ids=None, dependency_boundaries=None):
    """Close targets downward, then trace demand paths upward; no contract inference."""
    # Validate roots against the requested targets, not merely a shared descendant.
    seed = _plan_graph_v1(graph, target_ids, root_ids)
    nodes = graph["nodes"]
    full = copy.deepcopy(graph)
    for node in full["nodes"].values():
        node["selected"] = True
    components = [c for layer in layers(full) for c in layer]
    owners = {i: set(c) for c in components for i in c}
    boundaries = [] if dependency_boundaries is None else dependency_boundaries
    if not isinstance(boundaries, list):
        raise ValueError("dependency_boundaries must be a list")
    reasons = {}
    for entry in boundaries:
        if (not isinstance(entry, dict) or set(entry) != {"function_id", "reason"}
                or not isinstance(entry.get("function_id"), str)
                or entry["function_id"] not in nodes
                or not isinstance(entry.get("reason"), str) or not entry["reason"].strip()):
            raise ValueError("dependency boundary requires exact function_id and nonempty reason")
        ident = entry["function_id"]
        if ident in reasons:
            raise ValueError("duplicate dependency boundary")
        reasons[ident] = entry["reason"].strip()
    stops = set().union(*(owners[i] for i in reasons)) if reasons else set()
    original = set(seed["target_ids"])
    if original & stops:
        raise ValueError("dependency boundary cannot exclude a requested target SCC")
    adj = {i: set() for i in nodes}
    for edge in graph["edges"].values():
        adj[edge["caller"]].add(edge["callee"])
    processing = set(original); todo = list(original); encountered = set()
    while todo:
        for callee in adj[todo.pop()]:
            if callee in stops:
                encountered.update(owners[callee])
            elif callee not in processing:
                processing.add(callee); todo.append(callee)
    if stops - encountered:
        raise ValueError("dependency boundary is not reached from the target group")
    # Ancestors of newly included callees may add further demand branches.
    if stops & set(root_ids or []):
        raise ValueError("dependency boundary cannot exclude an explicit demand root")
    demand_graph = copy.deepcopy(graph)
    demand_graph["nodes"] = {i:n for i,n in graph["nodes"].items() if i not in stops}
    demand_graph["edges"] = {i:e for i,e in graph["edges"].items()
                             if e["caller"] not in stops and e["callee"] not in stops}
    plan = _plan_graph_v1(demand_graph, sorted(processing), root_ids)
    keep = set(plan["generation_ids"])
    boundary = [e for e in graph["edges"].values()
                if (e["caller"] in keep) != (e["callee"] in keep)]
    plan.update(
        context_ids=sorted({e["callee"] if e["caller"] in keep else e["caller"] for e in boundary}),
        boundary_edge_ids=sorted(e["id"] for e in boundary),
        excluded_incoming_edge_ids=sorted(e["id"] for e in boundary if e["callee"] in keep),
        outgoing_boundary_edge_ids=sorted(e["id"] for e in boundary if e["caller"] in keep),
    )
    target_graph = copy.deepcopy(full)
    target_graph["nodes"] = {i:n for i,n in full["nodes"].items() if i in processing}
    target_graph["edges"] = {i:e for i,e in full["edges"].items()
                             if e["caller"] in processing and e["callee"] in processing}
    proof_layers = list(reversed(layers(target_graph)))
    unknowns = [copy.deepcopy(u) for u in graph.get("unknown_calls", [])
                if u.get("caller") in processing]
    plan.update(
        version=VERSION,
        requested_target_ids=sorted(target_ids),
        scc_added_target_ids=seed["scc_added_target_ids"],
        dependency_added_target_ids=sorted(processing - original),
        dependency_boundaries=[{"function_id":i, "reason":reasons[i]} for i in sorted(reasons)],
        dependency_boundary_ids=sorted(stops),
        dependency_policy="downstream-scc-closure-with-explicit-unresolved-boundaries",
        target_unknown_calls=unknowns,
        dependency_status="unresolved" if stops or unknowns or graph.get("inventory_gaps") else "identified_edges_closed",
        generation_order="caller-first",
        proof_order_components=[c for layer in proof_layers for c in layer],
        proof_order_note="Dependency order only; not proof readiness or execution authorization",
    )
    return plan

def create_plan(root, source, target_ids, root_ids=None, dependency_boundaries=None):
    graph, identity = read_graph_run(root, source)
    plan = plan_graph(graph, target_ids, root_ids, dependency_boundaries)
    plan.update(source_run=str(Path(source).resolve()), source_graph_digest=digest(graph),
                input_snapshot_digest=digest(identity["input_snapshot"]),
                source_manifest_digest=digest(identity["manifest"]))
    plan["plan_digest"] = digest(plan)
    return plan, graph


def validate_plan(plan):
    value = copy.deepcopy(plan); actual = value.pop("plan_digest", None)
    if value.get("version") not in (1, VERSION) or actual != digest(value):
        raise ValueError("scope plan digest/version mismatch")
    return plan


def load_plan(root, path, manifest):
    plan = validate_plan(json.loads(Path(path).read_text()))
    graph, identity = read_graph_run(root, plan["source_run"])
    if (plan["source_graph_digest"] != digest(graph)
            or plan["input_snapshot_digest"] != digest(identity["input_snapshot"])
            or plan["source_manifest_digest"] != digest(manifest)):
        raise ValueError("scope plan source graph/input/manifest changed")
    expected = (_plan_graph_v1(graph, plan["requested_target_ids"], plan["root_ids"])
                if plan["version"] == 1 else
                plan_graph(graph, plan["requested_target_ids"], plan["root_ids"],
                           plan["dependency_boundaries"]))
    if any(plan.get(k) != v for k, v in expected.items()):
        raise ValueError("scope plan does not match recomputed demand paths")
    return plan, project(graph, plan)


def project(full, plan):
    """Keep only generation nodes in scheduling; retain boundary nodes separately."""
    g = copy.deepcopy(full)
    keep = set(plan["generation_ids"]); targets = set(plan["target_ids"])
    g["nodes"] = {i:n for i,n in g["nodes"].items() if i in keep}
    g["edges"] = {i:e for i,e in g["edges"].items() if e["caller"] in keep and e["callee"] in keep}
    for i, node in g["nodes"].items():
        node.update(role="target" if i in targets else "demand", selected=True, status="pending", spec=None)
        if plan["version"] >= 2:
            node["target_origin"] = ("requested" if i in plan["requested_target_ids"] else
                                     "dependency" if i in plan["dependency_added_target_ids"] else
                                     "recursive_peer" if i in targets else "upstream_demand")
        for key in ("review", "inherited"):
            node.pop(key, None)
    g["boundary_edges"] = [copy.deepcopy(full["edges"][i]) for i in plan["boundary_edge_ids"]]
    g["boundary_nodes"] = {i:copy.deepcopy(full["nodes"][i]) for i in plan["context_ids"]}
    for node in g["boundary_nodes"].values():
        node["role"] = "context"; node["selected"] = False
        node["context_trust"] = "Saved source material; any existing draft is unproved and not automatically applicable"
    for edge in list(g["edges"].values()) + g["boundary_edges"]:
        edge["requirements"] = []
    g["unknown_calls"] = [u for u in g.get("unknown_calls", []) if u.get("caller") in keep]
    for edge in g["boundary_edges"]:
        inside = edge["caller"] if edge["caller"] in keep else edge["callee"]
        g["unknown_calls"].append({"caller":inside, "edge_id":edge["id"],
            "reason":("Outgoing auxiliary dependency outside generation scope" if plan["version"] == 1 else
                      "Outgoing dependency outside generation scope; no verified contract applicability established") if edge["caller"] in keep
                     else "Incoming caller excluded by explicit scope boundary; its upstream demands are not covered",
            "boundary_caller":edge["caller"], "boundary_callee":edge["callee"]})
    g["scope_plan"] = copy.deepcopy(plan)
    for stale in ("continuation", "branch_scope"):
        g.pop(stale, None)
    g["layers"] = layers(g)
    g["components"] = [{"id":"scc-"+str(i), "members":c} for i,c in enumerate(c for l in g["layers"] for c in l)]
    return g


def render(plan, graph):
    lines = ["# 函数组需求范围计划", "", "待审核；未生成规约，未执行模型或证明。", "",
             "计划摘要：" + plan["plan_digest"], "",
             f"目标定义：{len(plan['target_ids'])}；上层需求函数：{len(plan['demand_ids'])}；边界背景：{len(plan['context_ids'])}。",
             f"递归分量新增目标：{len(plan['scc_added_target_ids'])}；被截断的上层调用边：{len(plan['excluded_incoming_edge_ids'])}。",
             f"原有未知记录：{plan['unknown_call_count']}；枚举缺口：{len(plan['inventory_gaps'])}。",
             "", "策略：" + plan["policy"], "", "未列入路径不表示没有依赖；平台变体和未知调用仍需审核。", "",
             "| 角色 | 函数 ID | 函数 | 源码 |", "|---|---|---|---|"]
    for role, ids in [("目标",plan["target_ids"]),("上层需求",plan["demand_ids"]),("边界背景",plan["context_ids"])]:
        for ident in ids:
            n=graph["nodes"][ident];src=n["source"]
            lines.append(f"| {role} | {ident} | {n['symbol']} | {src['path']}:{src['start']} |")
    if plan["version"] >= 2:
        lines += ["", "## 向下依赖范围", "",
                  f"用户指定：{len(plan['requested_target_ids'])}；向下新增：{len(plan['dependency_added_target_ids'])}。",
                  "向下新增目标：" + ", ".join(plan["dependency_added_target_ids"]),
                  "依赖状态：" + plan["dependency_status"] + "（不表示已具备证明条件）。",
                  "自然规约按调用者优先生成；下列分量按被调用者优先排列，仅供后续证明规划：",
                  json.dumps(plan["proof_order_components"], ensure_ascii=False),
                  "", "显式下层边界（含同一递归分量；未确认契约适用性）："]
        for entry in plan["dependency_boundaries"]:
            lines.append("- " + entry["function_id"] + "：" + entry["reason"])
        lines += ["", "目标未知调用：", json.dumps(plan["target_unknown_calls"], ensure_ascii=False, indent=2)]
    lines += ["", "## 边界调用", "", "| 边 ID | 调用者 | 被调用者 |", "|---|---|---|"]
    for ident in plan["boundary_edge_ids"]:
        e=graph["edges"][ident]
        lines.append(f"| {ident} | {e['caller']} | {e['callee']} |")
    return "\n".join(lines)+"\n"


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", default="input")
    parser.add_argument("--graph-run", required=True)
    parser.add_argument("--request", required=True, help="JSON: target_ids, optional root_ids and dependency_boundaries; exact IDs")
    parser.add_argument("--output", required=True)
    args=parser.parse_args()
    try:
        request=json.loads(Path(args.request).read_text())
        if not isinstance(request,dict) or set(request)-{"target_ids","root_ids","dependency_boundaries"}:
            raise ValueError("request accepts target_ids, root_ids and dependency_boundaries only")
        plan, graph=create_plan(args.input,args.graph_run,request.get("target_ids"),request.get("root_ids"),request.get("dependency_boundaries"))
        output=Path(args.output).resolve()
        if output.is_relative_to(Path(args.input).resolve()) or output.is_relative_to(Path(args.graph_run).resolve()):
            raise ValueError("plan output must be outside input/source run")
        output.mkdir(parents=True,exist_ok=False)
        write_json(output/"scope-plan.json",plan)
        write_json(output/"graph.json",project(graph,plan))
        write_text(output/"SCOPE.md",render(plan,graph))
        print(json.dumps({"plan":str(output/"scope-plan.json"),"plan_digest":plan["plan_digest"],
                          "targets":len(plan["target_ids"]),"generation":len(plan["generation_ids"])}))
    except (ValueError,OSError,KeyError) as exc:
        parser.error(str(exc))


if __name__ == "__main__":
    main()

"""Checkpoint bounded review batches without changing the recursive call graph."""
from collections import deque

from .schedule import digest, task_description


def member_order(members, nodes, outgoing, incoming, dependencies):
    component = set(members)

    def rank(ident):
        source = nodes[ident]["source"]
        return source["path"], source["line"], nodes[ident]["name"], ident

    roots = [ident for ident in members if dependencies[ident] - component or any(
        call["caller"] not in component for call in incoming[ident].values())]
    order, seen = [], set()
    for root in [*sorted(roots, key=rank), *sorted(members, key=rank)]:
        queue = deque([root])
        while queue:
            ident = queue.popleft()
            if ident in seen:
                continue
            order.append(ident)
            seen.add(ident)
            targets = {call["callee"] for call in outgoing[ident].values()} & component
            queue.extend(sorted(targets - seen, key=rank))
    return order


def member_keys(members, nodes, outgoing, incoming, dependencies, valid):
    component = sorted(members)
    return {ident: digest([component, task_description([ident], nodes, outgoing, incoming,
                                                        dependencies, valid, peers=members)])
            for ident in members}


def same_component_call(call, members):
    return call["kind"] == "internal" and call["caller"] in members and call["callee"] in members


def batch_task(batch, members, nodes, outgoing, incoming, dependencies, valid, materials):
    task = task_description(batch, nodes, outgoing, incoming, dependencies, valid, peers=members)
    calls = {**task["outgoing"], **task["incoming"]}
    task["component_members"] = sorted(members)
    task["peer_contracts"] = {}
    for ident in sorted(set(members) - set(batch)):
        record = valid.get(ident)
        related = {key for key, call in calls.items() if ident in (call["caller"], call["callee"])}
        if not related or not usable(record):
            continue
        draft = record["draft"]
        node = nodes[ident]
        source = node["source"]
        task["peer_contracts"][ident] = {"status": record["member_review"]["status"],
                                         "draft_digest": digest(draft),
                                         "source": {"path": materials.alias(node["library"], source["path"]),
                                                    "start": source["line"], "end": source["end_line"]},
                                         "cases": draft["cases"], "assumptions": draft["assumptions"],
                                         "call_requirements": [row for row in draft["call_requirements"]
                                                               if row["call_id"] in related]}
    return task


def usable(record):
    return bool(record and record.get("draft") and record["member_review"]["status"] != "blocked")


def peer_check_evidence(task, drafts, audit, checks):
    members = task["component_members"]
    digests = {ident: digest(draft) for ident, draft in drafts.items()}
    digests.update({ident: record["draft_digest"] for ident, record in task["peer_contracts"].items()})
    evidence = {}
    for key, row in audit.items():
        call = row["call"]
        if same_component_call(call, members) and not row["incomplete"]:
            evidence[key] = {"check": checks[key], "drafts": {ident: digests[ident]
                             for ident in (call["caller"], call["callee"])}}
    return evidence


def restore_checks(members, valid, calls):
    """Publish a reviewed SCC call on both endpoints while its two drafts match."""
    digests = {ident: digest(valid[ident]["draft"]) for ident in members if usable(valid.get(ident))}
    for ident in members:
        if ident in valid:
            base = valid[ident]["member_review"]
            valid[ident] = {**valid[ident], "status": base["status"],
                            "unverified_dependencies": list(base["unverified_dependencies"]),
                            "call_checks": dict(base["call_checks"])}
    for key, call in calls.items():
        if not same_component_call(call, members):
            continue
        endpoints = set((call["caller"], call["callee"]))
        active = endpoints & valid.keys()
        if not active:
            continue
        check = None
        if endpoints <= digests.keys():
            pair = {ident: digests[ident] for ident in endpoints}
            matching = [item["check"] for ident in sorted(active)
                        if (item := valid[ident]["member_review"]["peer_checks"].get(key))
                        and item["drafts"] == pair]
            if matching:
                order = {"compatible": 0, "unknown": 1, "conflict": 2}
                check = max(matching, key=lambda row: order[row["status"]])
        if check is None:
            reason = ("等待同一递归分量内的两个当前规约草案接受调用对照。" if endpoints <= digests.keys()
                      else "同一递归分量内的调用方或被调用方尚无经独立审核的可用草案。")
            check = {"call_id": key, "status": "unknown", "reason": reason}
        for ident in active:
            row = valid[ident]
            row["call_checks"][key] = check
            if check["status"] != "compatible":
                row["unverified_dependencies"].append(key)
                if check["status"] == "conflict":
                    row["status"] = "blocked"
                elif row["status"] == "approved":
                    row["status"] = "conditional"

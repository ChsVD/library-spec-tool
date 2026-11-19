"""Import Stage 2 and validate a deterministic, offline reference handoff."""

from collections import Counter, defaultdict
from hashlib import sha256
import json


def import_needs(stage2):
    checks = defaultdict(list)
    for owner, function in stage2["functions"].items():
        for call_id, check in function.get("call_checks", {}).items():
            checks[call_id].append({"saved_by": owner, "check": check})
    result = []
    for function_id, function in stage2["functions"].items():
        draft = function.get("draft")
        if draft is None:
            continue
        calls = []
        for requirement in draft["call_requirements"]:
            call_id = requirement["call_id"]
            call = stage2["calls"][call_id]
            if call["caller"] != function_id:
                raise ValueError(f"Wrong caller for {call_id}")
            calls.append({"call_id": call_id, "site": call, "requirement": requirement,
                          "checks": checks[call_id]})
        for ordinal, original in enumerate(draft["common_needs"], 1):
            encoded = json.dumps(original, ensure_ascii=False, sort_keys=True).encode()
            digest = sha256(encoded).hexdigest()[:16]
            result.append({
                "id": f"{function_id}:{ordinal}:{digest}",
                "function_id": function_id, "ordinal": ordinal, "original": original,
                "status": function["status"], "reason": function["reason"],
                "unverified_dependencies": function["unverified_dependencies"], "calls": calls,
            })
    return result


def commit_review(need, delivered, reply):
    """Accept only entry IDs explicitly delivered to the review test double."""
    by_id = {item["id"]: item for item in delivered}
    if reply["need_id"] != need["id"]:
        raise ValueError("Review addresses a different need")
    uses = []
    for assessment in reply["assessments"]:
        entry_id = assessment["entry_id"]
        if entry_id not in by_id:
            raise ValueError(f"Referenced entry was not delivered: {entry_id}")
        call_id = assessment["call_id"]
        if not any(call["call_id"] == call_id for call in need["calls"]):
            raise ValueError(f"Call does not belong to the need's function: {call_id}")
        item = by_id[entry_id]
        uses.append({
            **assessment, "need_id": need["id"], "target_validation": "not_run",
            "citation": {field: item[field] for field in ("path", "start", "end", "digest")},
        })
    referenced = {use["entry_id"] for use in uses}
    return {
        "coverage": "partial" if uses else "uncovered",
        "remaining": reply["remaining"], "uses": uses,
        "items": {key: item for key, item in by_id.items() if key in referenced},
    }


def stage2_summary(stage2, needs):
    return {
        "functions": len(stage2["functions"]), "common_needs": len(needs),
        "statuses": dict(Counter(f["status"] for f in stage2["functions"].values())),
        "formal_call_validation": stage2["formal_call_validation"],
        "stage1_result": stage2["stage1_result"],
    }


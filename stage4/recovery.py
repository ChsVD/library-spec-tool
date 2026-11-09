"""Recover a stopped role into a NEW run; preserve source reports and full validation."""
import copy
import hashlib
import json
from pathlib import Path
from dataclasses import asdict
from stage2.graph import digest
from .prompts import prompt
from . import strategies

VERSION = 1

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def prepare(previous, identity, inventory, nodes, budgets):
    previous = Path(previous).resolve(strict=True)
    load = lambda p: json.loads(p.read_text())
    old = load(previous/"identity.json")
    old_limit = old.get("max_report_chars", 24000)
    expected = dict(identity)
    expected["max_report_chars"] = old_limit
    expected["prompt_digest"] = digest({r:prompt(r,{},old_limit,bool(old.get("component_policy"))) for r in ("extract","common","review")})
    # Pre-feature runs have neither key; all other identity fields must match.
    if "max_report_chars" not in old: expected.pop("max_report_chars")
    if "recovery_policy" not in old: expected.pop("recovery_policy")
    if old != expected or load(previous/"input_snapshot.json") != inventory:
        raise ValueError("recovery rejects changed input, target scope, model or instructions")
    state=load(previous/"status.json");data=load(previous/"checkpoint.json")
    if state.get("status") not in ("incomplete","interrupted") or state.get("checkpoint_digest") != digest(data):
        raise ValueError("recovery requires a stopped consistent checkpoint")
    if not set(data["extracts"]) <= set(nodes):
        raise ValueError("recovery extraction scope changed")
    for ident, report in data["extracts"].items():
        if load(previous/"functions"/ident/"common_needs.json") != report:
            raise ValueError("completed extraction differs from checkpoint")
    task_rows=sorted(state["tasks"])
    # IDs contain the global numeric attempt suffix, not chronological role order.
    task_rows.sort(key=lambda name:int(name.rsplit("-",1)[1]))
    if not task_rows: raise ValueError("no stopped task to recover")
    task=previous/"tasks"/task_rows[-1];stopped=load(task/"status.json")
    role=stopped.get("role")
    if role not in ("extract","common","review") or stopped.get("status") in ("running","task_completed"):
        raise ValueError("latest task is not a stopped generation/review role")
    if stopped.get("budgets") != asdict(budgets):
        raise ValueError("recovery must preserve task budgets; report limit is separate")
    if data.get("review") is not None and (role!="common" or data["review"].get("verdict")!="needs_revision"):
        raise ValueError("recovery cannot bypass an accepted semantic review verdict")
    # Check saved report against assistant finish/patch history, never trust an edited draft alone.
    history=[json.loads(l) for l in (task/"conversation.jsonl").read_text().splitlines()]
    assembled=None
    for message in history:
        if message.get("role")!="assistant":continue
        try: action=json.loads(message["content"])
        except (ValueError,TypeError):continue
        if not isinstance(action,dict):continue
        if action.get("tool")=="finish" and isinstance(action.get("report"),dict):
            assembled=copy.deepcopy(action["report"])
        elif action.get("tool")=="patch_report" and isinstance(assembled,dict):
            changes=action.get("changes")
            if isinstance(changes,dict) and changes and set(changes)<=set(assembled):
                assembled.update(copy.deepcopy(changes))
    checkpoint=stopped.get("latest_checkpoint")
    revalidate=False
    if checkpoint:
        path=(task/checkpoint).resolve(strict=True)
        if not path.is_relative_to(task):raise ValueError("checkpoint escapes task")
        saved=load(path)
        if saved.get("kind")=="report":
            if saved.get("content")!=assembled or saved.get("role")!=role or saved.get("task_id")!=stopped.get("task_id"):
                raise ValueError("saved report differs from original assistant report")
            revalidate=True
    if data.get("candidate") is not None:
        if role not in ("common","review") or load(previous/"candidate.json")!=data["candidate"]:
            raise ValueError("candidate/review checkpoint mismatch")
        strategies.verify_export(data["candidate"], previous)
    protected={str(f):sha(f) for f in previous.rglob("*") if f.is_file() and f.name!="run.lock"}
    record={"version":VERSION,"source_run":str(previous),"source_task":str(task),"role":role,
            "source_sha256":protected,"extracts_reused":list(data["extracts"]),
            "old_report_limit":old_limit,"new_report_limit":identity["max_report_chars"],
            "revalidate_saved_report":revalidate,
            "instruction":"Repair the preserved report according to validation errors. Never relax scope, inherited assumptions, evidence or proof-status checks."}
    return copy.deepcopy(data), task, record

def recheck(record):
    if any(sha(Path(name))!=value for name,value in record["source_sha256"].items()):
        raise ValueError("recovery source files changed during recovery")

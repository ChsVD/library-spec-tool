"""Run the v2 pipeline with a mandatory read of the experiment top-level spec."""
import datetime
import hashlib
import json
from pathlib import Path
import sys
import time

base = Path(__file__).resolve().parent
root = base.parents[1]
sys.path.insert(0, str(root))
from stage2.codex_backend import CodexModel
from stage2.pipeline import run

stage1 = base / "stage1/link-evidence-stage1.json"
suffix = "link-evidence-clarified"
contracts = base / "inputs/reuse-contracts.json"
graph = json.loads(stage1.read_text())["graph"]
background = [base / "inputs/TOPLEVEL_SPEC.md", root / "example/minimal-simplex/references/fme"]
model = "gpt-6.1-sol"
effort = "high"

def log(event, **fields):
    entry = dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(), event=event, **fields)
    with (base / f"stage2-{suffix}-events.jsonl").open("a", encoding="utf-8") as f:
        print(json.dumps(entry, ensure_ascii=False), file=f, flush=True)

def factory(role, task):
    names = [graph["nodes"][i]["name"] for i in task.split(",")]
    engine = CodexModel(model=model, reasoning_effort=effort)
    calls = 0

    def exchange(messages, timeout):
        nonlocal calls
        if len(messages) == 2:
            payload = json.loads(messages[1]["content"])
            log("seed_top_level_read", task=names, role=role)
            reads = [
                {"tool":"read","path":payload["background_paths"][0],"start":1,"count":200},
                {"tool":"read","path":"project/target/include/sx_solver.h","start":1,"count":30},
                {"tool":"read","path":"project/target/src/backend.h","start":1,"count":30},
                {"tool":"read","path":"project/target/src/solver.c","start":1,"count":11},
                {"tool":"read","path":"project/target/vendor/gmp/minigmp/gmp_def.h","start":55,"count":22},
            ]
            return json.dumps({"tool":"batch","actions":reads})
        if len(messages) == 4:
            first = json.loads(messages[3]["content"])
            excerpt = first.get("results", [{}])[0].get("result", {})
            if "error" in excerpt or excerpt.get("truncated") is not False:
                raise RuntimeError("required top-level spec was not delivered completely")
        data = json.loads(messages[1]["content"])
        data["experiment_requirements"] = (
            "TOPLEVEL_SPEC.md was delivered by the first tool read and is the normative top-level input. "
            "Its promised normal-return rational feasibility and returned resources are the task goal. "
            "The graph was built natively on Linux x86-64 LP64. The intended historical verification "
            "contract/model is QCP Arch32 BigEndian. Write natural requirements with these distinct "
            "scopes and state any unverified reuse or model translation explicitly. "
            "GMP FME in background/1 is ordinary reference only. "
            "The explicit C linkage evidence resolves symbol ownership only, not proof-model compatibility. "
            "The directly delivered reuse contracts are the original Arch32 evidence; record unknown or "
            "conditional if their application would require proving compatibility with LP64 or missing premises. "
            "Use the initial source and pre-read materials, and make further Reader requests only for facts "
            "that affect the current function's actual contract or audit. When a necessary fact cannot "
            "be obtained promptly, report it as a concrete gap and return the required report. "
            "Never let reading exhaust the exchange before giving a report. Preserve a short description "
            "of each call condition, resources available and guarantees needed without copying entire contracts."
        )
        prompt = [{**m} for m in messages]
        if role == "review":
            prompt[0]["content"] += (
                "\nReport validation rule: every audit_calls row whose incomplete field is true "
                "must have status unknown, or conflict if there is evidence of an actual conflict. "
                "status compatible is invalid for incomplete rows, including external calls even "
                "when a plausible conditional contract can be described. Explain assumptions in reason. "
                "Apply this to every incomplete row before returning the report."
            )
        prompt[1]["content"] = json.dumps(data,ensure_ascii=False)
        calls += 1
        log("model_call_start", task=names, role=role, number=calls)
        t = time.monotonic()
        try:
            raw = engine(prompt, timeout=timeout)
        except Exception as exc:
            log("model_call_error", task=names, role=role, number=calls,
                seconds=round(time.monotonic()-t, 2), error=str(exc))
            raise
        action = json.loads(raw)
        log("model_call_end", task=names, role=role, number=calls,
            action=action.get("tool"), seconds=round(time.monotonic()-t, 2))
        return raw
    return exchange

model_identity = dict(
    backend="codex", model=model, reasoning_effort=effort,
    experiment_driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    reviewer_clarification="Since v2 rejects compatible for incomplete audit rows, report unknown or evidence-based conflict for those rows.",
)
if "--fork" in sys.argv:
    source = base / "stage2-link-evidence/stage2.json"
    text = source.read_bytes()
    previous = json.loads(text)
    old_identity = previous["identity"]["model"].copy()
    assert previous["status"] == "in_progress" and len(previous["functions"]) == 13
    assert previous["stage1_result"] == str(stage1)
    assert old_identity == dict(
        backend="codex", model=model, reasoning_effort=effort,
        experiment_driver_sha256=hashlib.sha256((base/"run_stage2_link_evidence.py").read_bytes()).hexdigest(),
    )
    fork = base/f"stage2-{suffix}"
    fork.mkdir(exist_ok=False)
    previous["identity"]["model"] = model_identity
    (fork/"stage2.json").write_text(json.dumps(previous,ensure_ascii=False,indent=2)+"\n")
    (base/"CHECKPOINT_FORK.json").write_text(json.dumps(dict(
        start_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        preserved_source=str(source), source_sha256=hashlib.sha256(text).hexdigest(),
        prior_submitted_functions=13, prior_model_identity=old_identity,
        new_checkpoint=str(fork/"stage2.json"), new_model_identity=model_identity,
        change="Review response status reminder only. Existing stage-two validated function drafts and checks retained verbatim. Stage-one graph, source, contracts, writer prompts and v2 validator unchanged.",
    ),ensure_ascii=False,indent=2)+"\n")
    log("checkpoint_forked", previous_submitted=13, reason="schema clarification for incomplete audit calls")

try:
    result = run(stage1_result=stage1, output=base/f"stage2-{suffix}", model_factory=factory,
                 background=background, reuse_contracts=contracts,
                 resume=("--resume" in sys.argv or "--fork" in sys.argv),
                 max_chars=140_000, timeout=900, max_revisions=1, model_identity=model_identity)
except Exception as exc:
    log("pipeline_error", error=str(exc))
    print(f"{type(exc).__name__}: {exc}", file=sys.stderr)
    sys.exit(1)
print(json.dumps({"status":result["status"],"functions":len(result["functions"])},ensure_ascii=False))
sys.exit(0 if result["status"]=="completed" else 2)

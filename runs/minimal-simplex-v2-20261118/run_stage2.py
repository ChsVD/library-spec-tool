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

stage1 = base / "stage1/stage1.json"
if "--adapted" in sys.argv:
    stage1 = base / "stage1/link-evidence-stage1.json"
suffix = "link-evidence" if "--adapted" in sys.argv else "native"
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
            return json.dumps({"tool":"read","path":payload["background_paths"][0],"start":1,"count":200})
        if len(messages) == 4:
            excerpt = json.loads(messages[3]["content"])
            if "error" in excerpt or excerpt["truncated"]:
                raise RuntimeError("required top-level spec was not delivered completely")
        data = json.loads(messages[1]["content"])
        data["experiment_requirements"] = (
            "TOPLEVEL_SPEC.md was delivered by the first tool read and is the normative top-level input. "
            "Its promised normal-return rational feasibility and returned resources are the task goal. "
            "The graph was built natively on Linux x86-64 LP64. The intended historical verification "
            "contract/model is QCP Arch32 BigEndian. Write natural requirements with these distinct "
            "scopes and state any unverified reuse or model translation explicitly. "
            "GMP FME in background/1 is ordinary reference only."
        )
        prompt = [{**m} for m in messages]
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

try:
    result = run(stage1_result=stage1, output=base/f"stage2-{suffix}", model_factory=factory,
                 background=background, reuse_contracts=contracts if suffix=="link-evidence" and contracts.is_file() else None,
                 resume="--resume" in sys.argv, max_chars=140_000, timeout=900, max_revisions=1,
                 model_identity=dict(backend="codex", model=model, reasoning_effort=effort,
                                     experiment_driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()))
except Exception as exc:
    log("pipeline_error", error=str(exc))
    print(f"{type(exc).__name__}: {exc}", file=sys.stderr)
    sys.exit(1)
print(json.dumps({"status":result["status"],"functions":len(result["functions"])},ensure_ascii=False))
sys.exit(0 if result["status"]=="completed" else 2)

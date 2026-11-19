"""Exercise the full queue and resume path with deterministic gap reports."""
import json
from pathlib import Path
import tempfile

from stage3.pipeline import run

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "runs/minimal-simplex-v2-20261118/stage2-link-evidence-clarified/stage2.json"


def factory(role, ident):
    def reply(messages, timeout):
        if role == "write":
            report = dict(need_id=ident, items=[], item_ids=[], disposition="gap",
                          coverage="uncovered", scope="Scheduling fixture",
                          call_ids=[], object_mapping=[], conditions=[],
                          remaining=["No semantic evaluation in this scheduling fixture."],
                          evidence_ids=[], references=[],
                          search={"status": "unnecessary", "reason": "Fixed scheduling fixture."})
        else:
            report = dict(need_id=ident, decision="accept", coverage="uncovered", reason="Fixed response.",
                          checks=dict.fromkeys(("direction", "target_conditions", "dependencies", "content"), "gap"),
                          findings=[], upstream_questions=[])
        return json.dumps({"tool": "finish", "report": report})
    return reply


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as folder:
        kwargs = dict(stage2_result=SOURCE, output=Path(folder)/"out", model_factory=factory)
        prefix = run(**kwargs, max_needs=17)
        assert len(prefix["uses"]) == 17
        end = run(**kwargs, resume=True)
        assert len(end["uses"]) == len(end["needs"]) == 60
        assert sum(row["usage"]["model_requests"] for row in end["uses"].values()) == 120
        assert all(row["coverage"] == "uncovered" and row["target_validation"] == "not_run"
                   for row in end["uses"].values())
        assert run(**kwargs, resume=True)["uses"] == end["uses"]
        print(json.dumps(end["summary"]))

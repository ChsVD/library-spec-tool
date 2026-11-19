"""Generate and independently review public proof material from a Stage 2 handoff."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from .offline import commit_review, import_needs, stage2_summary
from .references import ReferenceIndex


def run(stage2_path, reference, fixture):
    stage2_data = stage2_path.read_bytes()
    stage2 = json.loads(stage2_data)
    needs = import_needs(stage2)
    stage1 = json.loads(Path(stage2["stage1_result"]).read_bytes())
    nodes = stage1["graph"]["nodes"]
    need, = (n for n in needs if n["ordinal"] == fixture["ordinal"]
             and nodes[n["function_id"]]["name"] == fixture["function"])
    eligible = [call for call in need["calls"] if call["site"]["location"] == fixture["location"]]
    call, = eligible
    index = ReferenceIndex(reference)
    delivered = []
    assessments = []
    searches = {}
    for trial in fixture["trials"]:
        query = trial["query"]
        cards = index.search(**query)
        ranking = index.search(**{**query, "limit": len(index.entries)})
        searches[trial["direction"]] = {"query": query, "top_five": cards, "ranking": ranking}
        entry = index.read_entry(cards[trial["review_rank"] - 1]["id"])
        if entry["name"] != trial["expected_entry"]:
            raise ValueError(f"Review fixture does not describe the selected entry: {entry['name']}")
        delivered.append(entry)
        assessments.append({
            "entry_id": entry["id"], "call_id": call["call_id"],
            "direction": trial["direction"], **trial["assessment"],
        })
    review = {"need_id": need["id"], "assessments": assessments, "remaining": fixture["remaining"]}
    return {
        "schema_version": 1, "mode": "offline_fixed_review_fixture", "need": need,
        "stage2": stage2_summary(stage2, needs),
        "identity": {"stage2_sha256": sha256(stage2_data).hexdigest(), "reference_sha256": index.digest},
        "index": {"path": str(reference), "declarations": len(index.entries),
                  "parsed_entailments": sum(e["structure"] is not None for e in index.entries.values())},
        "searches": searches, "delivered": delivered, "review": review,
        **commit_review(need, delivered, review),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage2", type=Path, required=True, help="stage2.json")
    parser.add_argument("--stage1", type=Path, help="override the path to the bound stage1.json")
    parser.add_argument("--references", type=Path, help="JSON library manifest; omitted for an empty reference library")
    parser.add_argument("--top-level-spec", type=Path, help="optional target specification")
    parser.add_argument("--background", type=Path, action="append", default=[],
                        help="supplemental material, repeatable")
    parser.add_argument("--output", type=Path, required=True, help="output directory in production mode")
    parser.add_argument("--need-id", action="append", default=[], help="process only the selected need IDs, repeatable")
    parser.add_argument("--max-needs", type=int, help="process at most this many queued needs during this invocation")
    parser.add_argument("--resume", action="store_true", help="resume from the existing output directory")
    parser.add_argument("--model", default="gpt-6.2-sol")
    parser.add_argument("--reasoning-effort", choices=("low", "medium", "high", "xhigh", "max"), default="high")
    parser.add_argument("--timeout", type=float, default=600, help="seconds per need across generation and audit")
    parser.add_argument("--context-chars", type=int, default=100_000)
    parser.add_argument("--max-requests", type=int, default=24, help="model requests per need")
    parser.add_argument("--max-read-chars", type=int, default=60_000, help="reference source characters per need")
    parser.add_argument("--max-reads", type=int, default=24, help="reference excerpt deliveries per need")
    parser.add_argument("--max-files", type=int, default=12, help="reference files read per need")
    parser.add_argument("--max-revisions", type=int, default=1)
    parser.add_argument("--reference", type=Path, help="single reference file for the offline fixture")
    parser.add_argument("--fixture", type=Path, help="explicit offline mode; --output is a new JSON file")
    args = parser.parse_args(argv)
    if bool(args.fixture) != bool(args.reference):
        parser.error("--reference and --fixture must be used together for offline mode")

    try:
        if args.fixture:
            if args.resume or args.references or args.need_id or args.max_needs:
                parser.error("offline fixture mode does not take production selection or resume options")
            fixture = json.loads(args.fixture.read_bytes())
            result = run(args.stage2, args.reference, fixture)
            with args.output.open("x", encoding="utf-8") as stream:
                json.dump(result, stream, ensure_ascii=False, indent=2)
                stream.write("\n")
            return 0

        from .exchange import Limits
        from .model import Stage3CodexModel
        from .pipeline import run as run_production

        state = run_production(
            stage2_result=args.stage2, stage1_result=args.stage1, reference_manifest=args.references,
            top_level_spec=args.top_level_spec, background=args.background, output=args.output,
            resume=args.resume, need_ids=args.need_id, max_needs=args.max_needs,
            limits=Limits(timeout=args.timeout, context_chars=args.context_chars, max_requests=args.max_requests,
                          max_read_chars=args.max_read_chars, max_reads=args.max_reads, max_files=args.max_files,
                          max_revisions=args.max_revisions),
            model_factory=lambda *_: Stage3CodexModel(args.model, reasoning_effort=args.reasoning_effort),
            model_identity={"backend": "codex", "model": args.model, "reasoning_effort": args.reasoning_effort,
                            "session": "ephemeral", "isolation": "bubblewrap"},
            progress=lambda ident, status: print(f"{status} {ident}", file=sys.stderr, flush=True),
        )
    except KeyboardInterrupt:
        parser.exit(130, "stage3 interrupted; resume with the same output directory and inputs\n")
    except (KeyError, TypeError, ValueError, OSError, RuntimeError) as exc:
        parser.exit(1, f"stage3: {exc}\n")

    print(json.dumps({"status": state["status"], **state["summary"]}, ensure_ascii=False))
    if args.need_id:
        return 0 if all(state["uses"].get(ident, {}).get("status") == "accepted" for ident in args.need_id) else 2
    return 2 if state["status"] == "partial" else 0


if __name__ == "__main__":
    raise SystemExit(main())


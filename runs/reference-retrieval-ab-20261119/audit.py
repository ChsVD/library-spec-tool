#!/usr/bin/env python3
"""Validate the paired transcript, evidence and reading budgets; no model calls."""
import argparse
from collections import Counter
from pathlib import Path
import json

from trial import ROOTS, RUN, compact, dump, load, verified_index

PHASES = ("01-files", "02-declarations", "03-read")


def last_json(path):
    return json.loads(path.read_text().rstrip().rsplit("\n", 1)[-1])


def audit_group(base, ids, sources):
    rows = []
    for q in ids:
        packs = {}
        for mode in ("A", "B"):
            run = base / q / mode
            pack = last_json(run / "01-files.txt")
            directory_chars = len(compact(pack.pop("prebuilt_directory"))) if mode == "B" else 0
            assert "prebuilt_directory" not in pack
            packs[mode] = pack
            ids_in_inventory = {p[0] for paths in pack["modules_and_files"].values() for p in paths}
            fids = [entry["id"] for entry in load(run / "01-files.result.json")["files"]]
            assert set(fids) <= ids_in_inventory and len(set(fids)) == len(fids) <= 3
            menus = last_json(run / "02-declarations.txt")
            assert list(menus) == fids
            reads = load(run / "02-declarations.result.json")["read"]
            evidence = load(run / "evidence.json")
            assert reads == [d["id"] for d in evidence] and len(set(reads)) == len(reads) <= 6
            assert evidence == last_json(run / "03-read.txt")
            for d in evidence:
                fid, _ = d["id"].split("/")
                assert fid in fids and d["path"] == sources[fid]["path"]
                assert d["id"] in {item[0] for item in menus[fid]["items"]}
                lib, relative = d["path"].split("/", 1)
                lines = (ROOTS[lib] / relative).read_text(errors="replace").split("\n")
                assert d["source"] in "\n".join(lines[d["start"] - 1:d["end"]])
            judgement = load(run / "03-read.result.json")
            cite = judgement["entry"]
            prefix = judgement["prefix_needed"]
            if cite is not None:
                assert cite in reads and judgement["file"] == evidence[reads.index(cite)]["path"]
                assert reads.index(cite) < prefix <= len(reads)
            else:
                assert prefix is None
            totals = Counter()
            for phase in PHASES:
                p = run / f"{phase}.events.jsonl"
                events = [json.loads(line) for line in p.read_text().splitlines()]
                assert all(event["item"]["type"] in {"agent_message", "reasoning", "plan"}
                           for event in events if "item" in event)
                assert events[-1]["type"] == "turn.completed"
                assert events[-1]["usage"] == load(run / f"{phase}.cost.json")["usage"]
                totals.update(events[-1]["usage"])
            budget = load(run / "budget.json")
            assert budget["files"] == len(fids) and budget["declarations"] == len(reads)
            assert budget["source_chars"] == sum(len(e["source"]) for e in evidence)
            assert budget["directory_chars"] == directory_chars
            rows.append({
                "case": q, "mode": mode, "shortlist": [sources[f]["path"] for f in fids],
                "declarations": [d["name"] for d in evidence], "model_status": judgement["status"],
                "first_cited_file_rank": fids.index(cite.split("/")[0]) + 1 if cite else None,
                "first_cited_declaration_rank": reads.index(cite) + 1 if cite else None,
                "model_reported_confirmation_prefix": prefix,
                "confirmation_prefix_source_chars": sum(len(e["source"]) for e in evidence[:prefix])
                if prefix is not None else None,
                "budget": budget, "model_usage": dict(totals),
            })
        assert packs["A"] == packs["B"], f"Unequal lexical packets in {q}"
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    sources = {row["id"]: row for row in verified_index()}
    groups = {"main": audit_group(RUN / "results", ("Q1", "Q2", "Q3", "Q4a", "Q4b"), sources)}
    if args.replay:
        groups["q1_replay"] = audit_group(RUN / "q1-replay", ("Q1",), sources)
    dump(RUN / "audit.json", groups)
    print(f"{len(sources)} frozen files verified")
    for name, rows in groups.items():
        print(f"{name}: {len(rows)} outcomes with {len(PHASES) * len(rows)} tool-free completed sessions")
        for mode in ("A", "B"):
            selected = [r for r in rows if r["mode"] == mode]
            print(mode, "entries", sum(r["budget"]["declarations"] for r in selected),
                  "source_chars", sum(r["budget"]["source_chars"] for r in selected),
                  "input_tokens", sum(r["model_usage"]["input_tokens"] for r in selected))


if __name__ == "__main__":
    main()

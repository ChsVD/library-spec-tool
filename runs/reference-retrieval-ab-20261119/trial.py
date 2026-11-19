#!/usr/bin/env python3
"""Frozen paired retrieval trial. Uses only the three allow-listed reference roots."""
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from pathlib import Path
import argparse
import json
import math
import os
import re
import shutil
import subprocess
import tempfile
import time

RUN = Path(__file__).resolve().parent
PROJECTS = RUN.parents[2]
SNAPSHOT = PROJECTS / "library-reading-trial-20261008"
ROOTS = {
    "mini-gmp": SNAPSHOT / "mini-gmp",
    "sm2": SNAPSHOT / "sm2",
    "fme": RUN.parents[1] / "example/minimal-simplex/references/fme",
}
SUFFIXES = {".c", ".h", ".v", ".strategies"}
ROCQ = re.compile(
    r"(?m)^\s*(?:(?:Local|Global|Program)\s+)?"
    r"(Definition|Fixpoint|Lemma|Theorem|Fact|Remark|Corollary|Proposition|Inductive|Record|Axiom)"
    r"\s+([\w']+)"
)
RULE = re.compile(r"(?m)^\s*id\s*:\s*(\d+)\b")
C = re.compile(
    r"(?m)^\s*(?:struct\s+(\w+)\s*\{|"
    r"(?:[A-Za-z_]\w*[ \t*]+)+(\w+)\s*\([^;{}]{0,500}\)"
    r"\s*(?=\{|;|/\*@))"
)
C_REPAIRED = re.compile(
    r"(?m)^(?:struct[ \t]+(\w+)\s*\{|"
    r"(?:[A-Za-z_]\w*[ \t\n*]+)+(\w+)\s*\([^;{}]{0,500}\)"
    r"\s*(?=\{|;|/\*@))"
)
WORD = re.compile(r"[A-Za-z][A-Za-z0-9_']*|[0-9]+")
SEPS = re.compile(r"_+|(?<=[a-z])(?=[A-Z])|(?<=[a-zA-Z])(?=\d)")
STOP = set("a an and as at be by can does for from has have in int is it no of on or out that the to was when with z".split())


def terms(s):
    for token in WORD.findall(s):
        value = token.lower()
        if value not in STOP and len(value) > 1:
            yield value
        for part in SEPS.split(token):
            if part != token and len(part) > 1 and part.lower() not in STOP:
                yield part.lower()


def stable_top(counts, n):
    return [key for key, _ in sorted(counts.items(), key=lambda x: (-x[1], x[0]))[:n]]


def digest(b):
    return sha256(b).hexdigest()


def dump(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


def load(path):
    return json.loads(path.read_text())


def module(path, library):
    if library == "mini-gmp":
        return library + "/" + path.parts[0]
    if len(path.parts) > 3 and path.parts[:2] == ("rocq", "vc"):
        return library + "/" + "/".join(path.parts[:3])
    return library + "/" + "/".join(path.parts[:-1])


def items(text, suffix, c_repaired=False):
    scanner = {".v": ROCQ, ".strategies": RULE}.get(suffix, C_REPAIRED if c_repaired else C)
    matches = list(scanner.finditer(text))
    for i, m in enumerate(matches):
        start = m.start() + len(m[0]) - len(m[0].lstrip())
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        source = text[start:end].rstrip()
        if suffix == ".v":
            kind, name = m.groups()
            if kind in {"Lemma", "Theorem", "Fact", "Remark", "Corollary", "Proposition", "Axiom"}:
                source = re.split(r"(?m)^\s*(?:[Pp]roof(?:\s+using [^.]+)?\s*\.|Admitted\.|Qed\.)", source, maxsplit=1)[0].rstrip()
            # Sentence terminator without consuming a qualified name or a decimal.
            terminator = re.search(r"(?<!\.)\.(?=\s|$)", source)
            if terminator:
                source = source[:terminator.end()]
        elif suffix == ".strategies":
            kind, name = "rule", m[1]
            source = re.split(r"(?m)^#include\b", source, maxsplit=1)[0].rstrip()
        else:
            kind, name = ("struct", m[1]) if m[1] else ("C", m[2])
            if kind == "C":
                contract_end = source.find("*/")
                brace = source.find("{")
                if contract_end != -1 and (brace == -1 or source.find("/*@") < brace):
                    source = source[:contract_end + 2]
                elif brace != -1:
                    source = source[:brace].rstrip()
            elif (brace := source.find("};")) != -1:
                source = source[:brace + 2]
        if not source:
            continue
        line = text.count("\n", 0, start) + 1
        yield {"id": f"D{i + 1:04}", "kind": kind, "name": name,
               "start": line, "end": line + source.count("\n"), "source": source}


def index(read_entries=False, c_repaired=False):
    result = []
    for library, root in ROOTS.items():
        paths = sorted(p for p in root.rglob("*") if p.is_file() and p.suffix in SUFFIXES)
        for path in paths:
            relative = path.relative_to(root)
            data = path.read_bytes()
            text = data.decode("utf-8", errors="replace")
            words = Counter(terms(text))
            path_terms = Counter(terms(str(relative)))
            declarations = list(items(text, path.suffix, c_repaired)) if read_entries else []
            result.append({
                "id": f"F{len(result) + 1:03}", "path": library + "/" + relative.as_posix(),
                "module": module(relative, library), "size": len(data), "sha256": digest(data),
                "words": words, "path_terms": path_terms, "entries": declarations,
            })
    return result


def sampled(seq, n, key=lambda x: x):
    seq = sorted(set(seq), key=key)
    if len(seq) <= n:
        return seq
    return [seq[round(i * (len(seq) - 1) / (n - 1))] for i in range(n)]


def prepare():
    files = index(read_entries=True)
    manifest = [{k: f[k] for k in ("id", "path", "module", "size", "sha256")} for f in files]
    dump(RUN / "frozen" / "source-manifest.json", manifest)
    modules = defaultdict(list)
    for f in files:
        modules[f["module"]].append(f)
    cards = []
    for name, group in sorted(modules.items()):
        samples = []
        take_paths = sampled([f["path"] for f in group], 11, lambda p: digest(p.encode()))
        counts = Counter()
        for f in group:
            counts.update(f["path_terms"].keys())
            if f["path"] not in take_paths:
                continue
            names = [d["name"] for d in f["entries"] if d["kind"] != "rule"]
            if f["path"].endswith(".strategies"):
                words = set(terms(" ".join(m.group(0) for m in re.finditer(
                    r"(?m)^\s*(?:left|right|check|action)\s*:[^\n]*",
                    "\n".join(d["source"] for d in f["entries"])
                ))))
                names = sorted(x for x in words if len(x) >= 5 and x.isidentifier())
            samples.append([f["id"], Path(f["path"]).name,
                            sampled(names, 9, lambda n: digest(n.encode()))])
        cards.append({"module": name, "files": len(group), "filename_terms": stable_top(counts, 12),
                      "sampled_files": samples})
    dump(RUN / "frozen" / "directory-input.json", cards)


def b25(counts, average, q):
    length = sum(counts.values())
    adjust = 1.2 * (0.3 + 0.7 * length / max(1, average))
    return sum(weight * 2.2 * counts[t] / (counts[t] + adjust)
               for t, weight in q.items() if counts[t])


def search(files, q):
    avg = sum(sum(f["words"].values()) for f in files) / len(files)
    df = Counter()
    for f in files:
        df.update(f["words"].keys() & q.keys())
    weights = {t: q[t] * math.log(1 + (len(files) - df[t] + 0.5) / (df[t] + 0.5)) for t in q}
    weights = {t: v for t, v in weights.items() if df[t]}
    scores = []
    for f in files:
        names = Counter(t for d in f["entries"] for t in terms(d["name"]) if d["kind"] != "rule")
        score = b25(f["words"], avg, weights)
        score += 1.3 * sum(weights[t] for t in f["path_terms"].keys() & weights.keys())
        score += 0.45 * sum(weights[t] for t in names.keys() & weights.keys())
        match = sorted(f["words"].keys() & weights.keys(), key=lambda t: (-weights[t], t))[:10]
        scores.append((score, f["id"], match))
    return sorted(scores, key=lambda row: (-row[0], row[1]))


def menu(f, q):
    items = f["entries"]
    counts = [Counter(terms(d["source"])) for d in items]
    df = Counter(t for c in counts for t in c.keys() & q.keys())
    weights = {t: q[t] * math.log(1 + (len(items) - df[t] + 0.5) / (df[t] + 0.5))
               for t in q if df[t]}
    avg = sum(sum(c.values()) for c in counts) / max(1, len(items))
    rows = []
    for i, (d, c) in enumerate(zip(items, counts)):
        names = set(terms(d["name"]))
        score = b25(c, avg, weights) + 2 * sum(weights[t] for t in names & weights.keys())
        match = sorted(c.keys() & weights.keys(), key=lambda t: (-weights[t], t))[:9]
        row = [f["id"] + "/" + d["id"], d["kind"], d["name"], d["start"], d["end"], match]
        rows.append((score, i, row))
    return [row for _, _, row in sorted(rows, key=lambda x: (-x[0], x[1]))[:28]]


def request(folder, phase, prompt, auth_dir):
    folder.mkdir(parents=True, exist_ok=True)
    (folder / (phase + ".txt")).write_text(prompt)
    cmd = [
        "codex", "exec", "--ephemeral", "--ignore-user-config", "--ignore-rules",
        "--skip-git-repo-check", "-m", "gpt-6.2-sol",
        "-c", "model_reasoning_effort=high", "-c", "approval_policy=never",
        "-c", 'web_search="disabled"', "-c", "suppress_unstable_features_warning=true", "--disable", "shell_tool",
        "--disable", "multi_agent", "--disable", "shell_snapshot",
        "--enable", "skip_host_skill_discovery", "-s", "read-only", "--json", "-",
    ]
    before = time.monotonic()
    proc = subprocess.run(
        cmd, input=prompt, text=True, capture_output=True, timeout=180,
        cwd=auth_dir / "work", env={**os.environ, "CODEX_HOME": str(auth_dir)},
    )
    (folder / (phase + ".events.jsonl")).write_text(proc.stdout)
    (folder / (phase + ".stderr.txt")).write_text(proc.stderr)
    messages, usage = [], None
    for line in proc.stdout.splitlines():
        event = json.loads(line)
        if "item" in event:
            item = event["item"]
            if item["type"] not in {"agent_message", "reasoning", "plan"}:
                raise ValueError(f"unexpected tool/action in {phase}: {item['type']}")
            if event["type"] == "item.completed" and item["type"] == "agent_message":
                messages.append(item["text"])
        if event["type"] == "turn.completed":
            usage = event["usage"]
    if proc.returncode or not messages or usage is None:
        raise RuntimeError(f"{phase} failed, see {folder}")
    answer = messages[-1]
    if answer.startswith("```"):
        answer = re.sub(r"^```(?:json)?\s*|\s*```$", "", answer)
    result = json.loads(answer)
    dump(folder / (phase + ".result.json"), result)
    dump(folder / (phase + ".cost.json"),
         {"prompt_chars": len(prompt), "seconds": round(time.monotonic() - before, 2), "usage": usage})
    return result


def compact(data):
    return json.dumps(data, ensure_ascii=False, separators=(",", ":"))


SHARED = """You are participating in the same bounded reference lookup protocol as another independent session.
Only use the supplied payload. No tools, external material, source access, or conversation context.
Return JSON as requested; no Markdown. The candidate source is a reference snapshot, not the target library.
Your job is to locate the first genuinely useful semantic correspondence for adapting the requested proof step,
including direction and limitations. Related terms or file names are insufficient as an answer.
"""


def directory_request(home):
    cards = load(RUN / "frozen" / "directory-input.json")
    prompt = """Write a terse English reference directory for future library readers.
No tools. Work only from the inventory: paths, sampled declared names and aggregated filename terms.
For each module give one sentence about observable topics or reusable material and one short note
about artifact kinds or evidentiary limits when helpful. Avoid inventing topics, proofs or assumptions.
No particular retrieval question has been given. Do not promote individual declarations or rule numbers.
Return one JSON object mapping each exact module path to a description of at most 45 words.
Inventory follows.
""" + compact(cards)
    directory = request(RUN / "directory", "summary", prompt, home)
    if set(directory) != {c["module"] for c in cards}:
        raise ValueError("directory omitted or invented modules")
    if not all(isinstance(v, str) and len(v.split()) <= 50 for v in directory.values()):
        raise ValueError("directory entry exceeds the compact description limit")
    dump(RUN / "frozen" / "directory.json", directory)


def case(q, mode, index_rows, directory, home, out):
    files = [f for f in index_rows if f["path"].split("/")[0] in q["libraries"]]
    by_id = {f["id"]: f for f in files}
    counter = Counter(terms(q["need"]))
    qterms = {term: 1 + math.log(n) for term, n in counter.items()}
    ranking = search(files, qterms)
    common = {
        "modules_and_files": defaultdict(list),
        "fulltext_plus_symbol_top30": [
            [fid, round(score, 2), matched] for score, fid, matched in ranking[:30]
        ],
    }
    for f in files:
        relative = f["path"][len(f["module"]) + 1:]
        common["modules_and_files"][f["module"]].append([f["id"], relative])
    if mode == "B":
        common["prebuilt_directory"] = {m: directory[m] for m in common["modules_and_files"]}
    folder = out / q["id"] / mode
    picked = request(folder, "01-files", SHARED + f"""
Current need: {q["need"]}
The shared file inventory and full-text/symbol ranking are below. The ranking includes matches and does
not prove relevance. Choose up to three file IDs in order of first read. You may choose any inventory ID.
For each give a short reason about the expected material. Output {{ "files": [{{"id":"F000","reason":"..."}}] }}.
""" + compact(common), home)["files"]
    fids = [f["id"] for f in picked]
    if len(fids) > 3 or len(set(fids)) != len(fids) or not set(fids) <= by_id.keys():
        raise ValueError(f"Invalid file selection: {picked}")
    menus = {f["id"]: {"path": f["path"], "items": menu(f, qterms)} for f in (by_id[k] for k in fids)}
    selected = request(folder, "02-declarations", SHARED + f"""
Current need: {q["need"]}
The files below were selected in order. Each row is [ID, kind, name or rule number,
start line, end line, matched query terms]. No statement has been read yet.
Choose up to six declaration IDs in the proposed read order, within these files.
Select only entries useful for verifying a correspondence or a required condition.
Do not use rule numbers as evidence of direction. Return {{ "read": ["F000/D0000"] }}.
""" + compact(menus), home)["read"]
    offered = {row[0] for f in menus.values() for row in f["items"]}
    if len(selected) > 6 or len(set(selected)) != len(selected) or not set(selected) <= offered:
        raise ValueError(f"Invalid declaration selection: {selected}")
    evidence = []
    for ident in selected:
        fid, did = ident.split("/")
        f = by_id[fid]
        d = next(d for d in f["entries"] if d["id"] == did)
        if len(d["source"]) > 10000:
            raise ValueError(f"{ident} exceeds full statement size limit")
        evidence.append({**d, "id": ident, "path": f["path"]})
    dump(folder / "evidence.json", evidence)
    request(folder, "03-read", SHARED + f"""
Current need: {q["need"]}
The source entries below, in read order, are your entire evidence. Give the earliest entry supporting
a usable correspondence (or explicitly none), and the earliest prefix of entries after which you can verify it.
State what the entry gives, direction, prerequisites, and what would still need adaptation.
A partial semantic correspondence is allowed if you name the missing part. Distinguish a related file,
an actual declaration, and checking preconditions/direction. For a strategy track the sides and changes.
Do not cite entries that were not read. Do not claim a target proof or a larger routine from a local step.
Return {{ "file": null, "entry": null, "prefix_needed": null, "status": "missing|partial|match",
"correspondence": "...", "direction": "...", "conditions_and_limits": "...", "additional_evidence": [] }}.
""" + compact(evidence), home)
    dump(folder / "budget.json", {
        "files": len(fids), "declarations": len(evidence),
        "source_chars": sum(len(e["source"]) for e in evidence),
        "source_lines": sum(e["end"] - e["start"] + 1 for e in evidence),
        "fulltext_candidates": min(30, len(files)),
        "directory_chars": len(compact(common["prebuilt_directory"])) if mode == "B" else 0,
    })
    print(q["id"], mode, fids, selected, flush=True)


def verified_index(c_repaired=False):
    files = index(read_entries=True, c_repaired=c_repaired)
    expected = load(RUN / "frozen" / "source-manifest.json")
    actual = [{k: f[k] for k in ("id", "path", "module", "size", "sha256")} for f in files]
    if actual != expected:
        raise RuntimeError("reference snapshot changed")
    return files


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("command", choices=("prepare", "directory", "run", "verify"))
    ap.add_argument("--ids", nargs="+")
    ap.add_argument("--out", type=Path, default=RUN / "results")
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--q1-c-scanner-replay", action="store_true")
    args = ap.parse_args()
    if args.q1_c_scanner_replay and (args.command != "run" or args.ids != ["Q1"] or args.out.resolve() == RUN / "results"):
        ap.error("C scanner repair can only run Q1 with a distinct output directory")
    if args.command == "prepare":
        prepare()
        return
    if args.command == "verify":
        print(len(verified_index()), "frozen source files verified")
        return
    if not (Path.home() / ".codex/auth.json").is_file():
        raise RuntimeError("local Codex ChatGPT auth is unavailable")
    with tempfile.TemporaryDirectory(prefix="library-retrieval-codex-") as auth_path:
        home = Path(auth_path)
        shutil.copy2(Path.home() / ".codex/auth.json", home / "auth.json")
        (home / "work").mkdir()
        if args.command == "directory":
            directory_request(home)
            return
        files = verified_index(args.q1_c_scanner_replay)
        directory = load(RUN / "frozen" / "directory.json")
        questions = load(RUN / "frozen" / "questions.json")
        jobs = [(q, mode) for q in questions if args.ids is None or q["id"] in args.ids for mode in ("A", "B")]
        if not jobs:
            raise ValueError("No matching questions")
        if any((args.out / q["id"] / mode).exists() for q, mode in jobs):
            raise ValueError("The selected output already exists; use a new --out directory")
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            tasks = [pool.submit(case, q, mode, files, directory, home, args.out) for q, mode in jobs]
            for task in tasks:
                task.result()


if __name__ == "__main__":
    main()

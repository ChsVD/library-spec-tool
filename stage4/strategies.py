"""Reference-only strategy attachments; never install or execute rules."""
import hashlib
from stage1.contracts import check_evidence, safe_id, nonempty
from stage1.task import write_json
from stage2.graph import digest

VERSION = 1


def validate(report, reader):
    rows = report.get("reference_strategies", [])
    if not isinstance(rows, list):
        return ["reference_strategies must be a list"]
    errors, ids = [], set()
    references = {r["id"] for r in report.get("references", [])}
    used = set()
    for row in rows:
        if not isinstance(row, dict):
            errors.append("strategy record must be an object"); continue
        ident = row.get("id")
        if not safe_id(ident) or ident in ids:
            errors.append("strategy requires unique safe id")
        if isinstance(ident, str): ids.add(ident)
        refs = row.get("reference_ids")
        if not isinstance(refs, list) or not refs or any(not isinstance(r,str) or r not in references for r in refs):
            errors.append("strategy reference_ids must reference existing definitions/lemmas")
        for field in ("dependencies", "applicability"):
            if not nonempty(row.get(field)):
                errors.append("strategy requires " + field)
        errors += check_evidence([row.get("source")], reader)
        proofs = row.get("proof_sources")
        if not isinstance(proofs, list):
            errors.append("strategy proof_sources must be a list")
        else:
            errors += check_evidence(proofs, reader, required=False)
            if not proofs and not nonempty(row.get("proof_unknown")):
                errors.append("missing strategy proof requires proof_unknown")
        if row.get("target_status") != "not_validated":
            errors.append("reference strategy cannot claim target validation")
    for item in report.get("items", []):
        links = item.get("strategy_ids", [])
        if not isinstance(links, list) or any(not isinstance(i,str) or i not in ids for i in links):
            errors.append("item strategy_ids must reference existing strategies")
        else:
            used.update(links)
    if ids - used:
        errors.append("reference strategies must be linked to candidate items")
    return errors


def export(report, reader, output):
    """Read via the same source boundary, copy line content, publish authoritative index."""
    folder = output / "reference_strategies"
    folder.mkdir(exist_ok=True)
    rows = []
    for row in report.get("reference_strategies", []):
        src = row["source"]
        lines, source_sha = reader.lines(src["path"])
        if not 1 <= src["start"] <= src["end"] <= len(lines):
            raise ValueError("strategy source range changed")
        data = ("\n".join(lines[src["start"]-1:src["end"]])+"\n").encode("utf-8")
        sha = hashlib.sha256(data).hexdigest()
        filename = row["id"]+"-"+sha+".strategies"
        (folder/filename).write_bytes(data)
        proofs = []
        for proof in row["proof_sources"]:
            _, proof_sha = reader.lines(proof["path"])
            proofs.append({**proof, "source_sha256": proof_sha})
        rows.append({**row, "source": {**src, "source_sha256": source_sha},
            "proof_sources": proofs, "file": filename, "sha256": sha,
            "item_ids": [i["id"] for i in report["items"] if row["id"] in i.get("strategy_ids", [])]})
    index = {"version": VERSION, "candidate_digest": digest(report),
             "target_status": "not_validated", "installed": False,
             "copy_format": "Selected source lines, UTF-8 with LF and final newline; not a standalone strategy package.",
             "strategies": rows}
    write_json(folder/"index.json", index)
    return index

def verify_export(report, output):
    import json
    folder = output / "reference_strategies"
    index = json.loads((folder/"index.json").read_text())
    if index.get("candidate_digest") != digest(report) or index.get("installed") is not False:
        raise ValueError("reference strategy index differs from candidate")
    expected = {r["id"] for r in report.get("reference_strategies", [])}
    if {r["id"] for r in index["strategies"]} != expected:
        raise ValueError("reference strategy coverage changed")
    for row in index["strategies"]:
        path = (folder/row["file"]).resolve()
        if not path.is_relative_to(folder.resolve()) or hashlib.sha256(path.read_bytes()).hexdigest() != row["sha256"]:
            raise ValueError("reference strategy attachment changed")

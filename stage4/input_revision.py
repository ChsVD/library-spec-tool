"""Explicit, exact allowlist for additive input changes."""
import copy,json
from pathlib import Path
from stage1.runner import snapshot
from stage2.graph import digest
from .recovery import sha
from . import strategies

def transition(root, source, original, path):
    manifest=json.loads(Path(path).read_text())
    if manifest.get("version")!=1 or Path(manifest["source_stage3_run"]).resolve()!=source or Path(manifest["new_root"]).resolve()!=root:
        raise ValueError("input transition root/upstream mismatch")
    baseline=Path(manifest["baseline_root"]).resolve(strict=True)
    if snapshot(baseline)!=original:raise ValueError("baseline input changed")
    inventory=snapshot(root)
    old={r["path"]:r["sha256"] for r in original};new={r["path"]:r["sha256"] for r in inventory}
    if any(new.get(k)!=v for k,v in old.items()):raise ValueError("original input modified or deleted")
    additions=manifest.get("added_files")
    if not isinstance(additions,list) or not additions:raise ValueError("explicit added_files required")
    allowed={}
    for row in additions:
        name=row.get("path")
        if not isinstance(name,str) or name in allowed or not row.get("origin"):
            raise ValueError("each addition requires unique path, hash and origin")
        allowed[name]=row.get("sha256")
    actual={k:v for k,v in new.items() if k not in old}
    if allowed!=actual:raise ValueError("added file allowlist/hash mismatch")
    return inventory,{"manifest":manifest,"manifest_digest":digest(manifest),
                      "baseline_snapshot_digest":digest(original),"new_snapshot_digest":digest(inventory)}

def seed(previous, graph, nodes, old_inventory, model):
    previous=Path(previous).resolve(strict=True)
    load=lambda name:json.loads((previous/name).read_text())
    identity=load("identity.json");data=load("checkpoint.json");state=load("status.json")
    if identity["model"]!=model or identity["graph_digest"]!=digest(graph):
        raise ValueError("revision seed model or upstream scope changed")
    if load("input_snapshot.json")!=old_inventory or state.get("checkpoint_digest")!=digest(data):
        raise ValueError("revision seed input/checkpoint mismatch")
    if state.get("status") not in ("partial","insufficient","needs_revision"):
        raise ValueError("revision requires reviewed candidate needing correction")
    if set(data["extracts"])!=set(nodes) or data["candidate"]!=load("candidate.json") or data["review"]!=load("review.json"):
        raise ValueError("revision candidate/extraction mismatch")
    for ident,value in data["extracts"].items():
        if load("functions/"+ident+"/common_needs.json")!=value:raise ValueError("extraction changed")
    strategies.verify_export(data["candidate"],previous)
    protected={str(f):sha(f) for f in previous.rglob("*") if f.is_file() and f.name!="run.lock"}
    return copy.deepcopy(data),{"source_run":str(previous),"source_sha256":protected,
                               "extracts_reused":list(data["extracts"])}

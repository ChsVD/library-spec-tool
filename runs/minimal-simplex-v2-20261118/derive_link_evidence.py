"""Derive separate native linkage evidence without changing the tool's original graph."""
import collections
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

base = Path(__file__).resolve().parent
sys.path.insert(0,str(base.parents[1]))
from stage1.graph import compute_scope

graph_path = base / "stage1/stage1.json"
original = json.loads(graph_path.read_text())
r = json.loads((graph_path.parent / "raw-graph.json").read_text())
solver = next(u for u in r["units"] if u["source"].endswith("/target/src/solver.c"))
decls = solver["declarations"]
native_db = json.loads((base / "inputs/compile_commands.json").read_text())
nodes = original["graph"]["nodes"]
locations = {
    (c["location"]["line"],c["location"]["column"]): decls[c["callee"]]
    for c in solver["calls"] if c["callee"] in decls
}

symbols = collections.defaultdict(list)
with tempfile.TemporaryDirectory(prefix="sx-link-evidence-") as work:
    objects = []
    for command in native_db:
        args = command["arguments"].copy()
        obj = Path(work) / Path(command["file"]).with_suffix(".o").name
        args[args.index("-o")+1] = str(obj)
        subprocess.run(args, cwd=command["directory"], check=True, capture_output=True)
        objects.append(str(obj))
        stdout = subprocess.check_output(["nm","-P","-g","--defined-only",str(obj)], text=True)
        for ln in stdout.splitlines():
            name, kind, *_ = ln.split()
            if kind == "T":
                symbols[name].append(command["file"])
    undefined = {ln.split()[0] for ln in subprocess.check_output(
        ["nm","-P","-u",str(Path(work)/"solver.o")],text=True).splitlines()}
    aggregate = Path(work) / "native-relocatable.o"
    subprocess.run(["cc","-r",*objects,"-o",str(aggregate)],check=True,capture_output=True)
    resolved_undefined = {ln.split()[0] for ln in subprocess.check_output(
        ["nm","-P","-u",str(aggregate)],text=True).splitlines()}

adapted = copy.deepcopy(original)
graph = adapted["graph"]
fixed = []
contract_ranges = {
    "mpz_init":(3,21), "mpz_clear":(233,243), "mpz_abs":(21,33), "mpz_neg":(15,27),
    "mpz_set":(39,51), "mpz_set_ui":(74,79), "mpz_gcd":(155,164), "mpz_divexact":(32,44),
    "mpz_mul":(87,115),"mpz_addmul":(60,68),
}
contracts = {}
for gap in original["coverage"]["scoped_analysis_gaps"]:
    if gap["reason"] != "unconfirmed_call_target" or len(gap.get("candidate_ids",[])) != 1:
        continue
    callee = gap["candidate_ids"][0]
    node = nodes[callee]
    if node["library"] != "minigmp" or node["status"]!="definition":
        continue
    loc = gap["location"]
    decl = locations[loc["line"],loc["column"]]
    if decl["type"] != node["type"] or decl["symbol"] != node["symbol"] or decl["linkage"] != "external":
        continue
    if not (decl["symbol"] in undefined and decl["symbol"] not in resolved_undefined):
        continue
    vendor = Path(original["libraries"]["minigmp"]["source_root"])
    implemented = vendor / node["source"]["path"]
    if symbols[decl["symbol"]] != [str(implemented)]:
        continue
    start,end = contract_ranges[decl["symbol"]]
    contracts[callee] = dict(path=str(implemented),start=start,end=end)
    evidence = dict(caller=gap["caller"],callee=callee,location=loc,source_declaration=decl["location"],
                    canonical_type=decl["type"],unique_native_defining_unit=str(implemented),
                    contract=contracts[callee],contract_source_sha256=hashlib.sha256(implemented.read_bytes()).hexdigest())
    fixed.append(evidence)
    edge = next((edge for edge in graph["edges"].values()
                 if edge["caller"]==gap["caller"] and edge["callee"]==callee),None)
    if edge is None:
        edge = dict(caller=gap["caller"],callee=callee,callsites=[])
        graph["edges"][f"link-evidence-{len(fixed):02d}"] = edge
    edge["callsites"].append(dict(**loc,kind="direct",evidence="experiment_explicit_native_linkage"))
    graph["analysis_gaps"].remove(gap)

assert len(fixed)==37 and len(contracts)==10
adapted["scope"] = compute_scope(graph, original["scope"]["entry_ids"])
reached = set(adapted["scope"]["reached_ids"])
adapted["coverage"]["scoped_analysis_gaps"] = [g for g in graph["analysis_gaps"] if g["caller"] in reached]
adapted["coverage"]["scoped_external_calls"] = [c for c in graph["external_calls"] if c["caller"] in reached]
adapted["status"] = ("partial_analysis" if adapted["coverage"]["scoped_analysis_gaps"] or
                     any(u["status"]!="parsed" for u in adapted["coverage"]["translation_units"])
                     else "analysis_completed")
adapted["provenance"]["experiment_native_linkage"] = {
    "based_on_sha256":hashlib.sha256(graph_path.read_bytes()).hexdigest(),
    "evidence_path":str(base/"inputs/NATIVE_LINK_EVIDENCE.json"),
    "scope":"C symbol linkage verified on native LP64 only; verified MiniGMP contracts are for Arch32 BigEndian, ABI applicability unverified.",
}
(base/"inputs/NATIVE_LINK_EVIDENCE.json").write_text(json.dumps(fixed,ensure_ascii=False,indent=2)+"\n")
(base/"inputs/reuse-contracts.json").write_text(json.dumps(contracts,ensure_ascii=False,indent=2)+"\n")
(graph_path.parent/"link-evidence-stage1.json").write_text(json.dumps(adapted,ensure_ascii=False,indent=2)+"\n")
print("linkage sites",len(fixed),"contracts",len(contracts),"reuse edges",len(adapted["scope"]["reuse_boundaries"]))
print("scope", sorted(nodes[i]["name"] for i in adapted["scope"]["function_ids"]))
print("gaps",len(adapted["coverage"]["scoped_analysis_gaps"]),"external",len(adapted["coverage"]["scoped_external_calls"]))

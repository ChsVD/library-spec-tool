"""Task-local upstream views and deterministic mandatory source delivery."""
import copy
from stage2.graph import digest

VERSION = 2


def source_ranges(value):
    """Coordinates are navigation only until delivered through this role's Reader."""
    if isinstance(value, dict):
        if (isinstance(value.get("path"), str) and type(value.get("start")) is int
                and type(value.get("end")) is int and 1 <= value["start"] <= value["end"]):
            yield {k:value[k] for k in ("path", "start", "end")}
        else:
            for child in value.values():
                yield from source_ranges(child)
    elif isinstance(value, list):
        for child in value:
            yield from source_ranges(child)


def read_actions(ranges):
    merged = []
    for item in sorted(ranges, key=lambda x:(x["path"],x["start"],x["end"])):
        if merged and item["path"] == merged[-1]["path"] and item["start"] <= merged[-1]["end"] + 1:
            merged[-1]["end"] = max(merged[-1]["end"], item["end"])
        else:
            merged.append(dict(item))
    return [{"tool":"read","path":x["path"],"start":start,"count":min(120,x["end"]-start+1)}
            for x in merged for start in range(x["start"],x["end"]+1,120)]


def local_context(upstream, graph, ids):
    ids = set(ids)
    value = copy.deepcopy(upstream)
    cards = {}
    index = {}
    def archive(key, rows):
        refs = []
        width = 8 if key in ("inventory_gaps","other_unknown_calls","other_boundary_edges") else 1
        for start in range(0,len(rows),width):
            ident = "background:" + key + ":" + str(start // width)
            cards[ident] = copy.deepcopy(rows[start] if width == 1 else rows[start:start+width])
            refs.append(ident)
        index[key] = {"count":len(rows),"artifact_ids":refs}
    all_edges = list(graph.get("edges",{}).values()) + graph.get("boundary_edges",[])
    edges = [e for e in all_edges if e.get("caller") in ids or e.get("callee") in ids]
    related = ids | {e.get(k) for e in edges for k in ("caller","callee")}
    value["expected_function_ids"] = sorted(ids)
    for key in ("conditions","demand_conditions"):
        original = upstream.get(key,{})
        value[key] = {i:copy.deepcopy(rows) for i,rows in original.items()
                      if i in (ids if key == "conditions" else related)}
        archive(key, [{"function_id":i,"conditions":rows} for i,rows in original.items()
                      if i not in value[key]])
    for key in ("demand_context","boundary_context"):
        original = upstream.get(key,[])
        archive(key, original)
        value[key] = []
        for i, node in enumerate(original):
            if node.get("id") not in related:
                continue
            card = {k:copy.deepcopy(v) for k,v in node.items() if k != "spec"}
            spec = node.get("spec") or {}
            # Preserve related caller assumptions in full; do not summarize their semantics.
            card["assumptions"] = spec.get("assumptions", "")
            card["conditional_assumptions"] = copy.deepcopy(spec.get("conditional_assumptions",[]))
            card["callee_requirements"] = [copy.deepcopy(x) for x in spec.get("callee_requirements",[])
                if not x.get("callee_id") or x["callee_id"] in ids]
            card["full_context"] = "background:" + key + ":" + str(i)
            value[key].append(card)
    unknowns = upstream.get("unknown_calls",[])
    value["unknown_calls"] = [copy.deepcopy(u) for u in unknowns
                             if not u.get("caller") or u.get("caller") in related]
    archive("other_unknown_calls", [u for u in unknowns if u not in value["unknown_calls"]])
    boundary = upstream.get("boundary_edges",[])
    relevant_boundary = [e for e in boundary if e in edges]
    value.pop("boundary_edges",None)
    value["boundary_edge_ids"] = [e["id"] for e in relevant_boundary]
    archive("other_boundary_edges", [e for e in boundary if e not in relevant_boundary])
    # Every relevant boundary edge remains complete in this single canonical table.
    value["call_requirements"] = copy.deepcopy(edges)
    # Inventory gaps have no reliable function ownership. Keep their global impact mandatory.
    gaps = upstream.get("inventory_gaps",[])
    archive("inventory_gaps", gaps)
    value["inventory_gaps"] = {
        "count":len(gaps), "status":"unresolved_global_scope" if gaps else "none_recorded",
        "instruction":"Unexpanded inventory gaps may affect every target/configuration; no complete-module or complete-configuration claim. Inspect indexed details before resolving applicability."}
    value["background_index"] = index
    value["background_trust"] = "Optional records are retained, not established irrelevant. Current direct requirements and related assumptions are mandatory; other branches may remain outside scope."
    if upstream.get("dependency_scope"):
        scope=upstream["dependency_scope"]
        archive("dependency_scope", [scope])
        value["dependency_scope"] = {
            "requested_target_ids":[i for i in scope.get("requested_target_ids",[]) if i in ids],
            "dependency_added_target_ids":[i for i in scope.get("dependency_added_target_ids",[]) if i in ids],
            "dependency_status":scope.get("dependency_status","unknown"),
            "note":"Whole-group dependency boundaries and order remain in the indexed record; no proof-readiness claim."}
    value["full_upstream_digest"] = digest(upstream)
    return value, cards


def needs_summary(nodes, artifacts):
    """Lossless question identities and conditions, without extraction evidence trees."""
    rows = []
    for ident, node in nodes.items():
        spec = node['spec']
        extracted = artifacts['extract:' + ident]
        upstream = copy.deepcopy(spec.get('common_needs', []))
        rows.append({
            'function_id':ident, 'source':copy.deepcopy(node['source']),
            'assumptions':copy.deepcopy(spec.get('assumptions', '')),
            'conditional_assumptions':copy.deepcopy(spec.get('conditional_assumptions', [])),
            'upstream_needs':{'present':'common_needs' in spec, 'items':upstream,
                              'ids':['upstream-' + str(i) for i in range(len(upstream))]},
            'needs':[{k:copy.deepcopy(n[k]) for k in ('id', 'function_id', 'spec_clause',
                       'use_site', 'search_question', 'source', 'upstream_need_id') if k in n}
                     for n in extracted['needs']],
            'spec_artifact':'spec:' + ident, 'extract_artifact':'extract:' + ident})
    return {'schema_version':1, 'material_policy':VERSION, 'functions':rows}


def compact_call_context(context, optional):
    """Keep requirements/conditions mandatory; archive bulky callsite navigation."""
    for index, edge in enumerate(context['call_requirements']):
        ident = 'background:call_requirements:' + str(index)
        optional[ident] = copy.deepcopy(edge)
        context['call_requirements'][index] = {
            k:copy.deepcopy(v) for k,v in edge.items()
            if k not in ('callsites', 'callsite', 'code', 'excerpt', 'snippet', 'source_text')}
        context['call_requirements'][index]['full_context'] = ident
    context['background_index']['call_requirements'] = {
        'count':len(context['call_requirements']),
        'artifact_ids':['background:call_requirements:' + str(i)
                        for i in range(len(context['call_requirements']))]}


def prepare(role, graph, nodes, upstream, artifacts, scoped=None, source_preparation=None,
            protocol_version=3):
    if protocol_version == 3:
        return prepare_v3(role, graph, nodes, upstream, artifacts, scoped, source_preparation)
    return prepare_legacy(role, graph, nodes, upstream, artifacts, scoped, source_preparation)


def prepare_v3(role, graph, nodes, upstream, artifacts, scoped=None, source_preparation=None):
    if role == 'extract':
        return prepare_legacy(role, graph, nodes, upstream, artifacts, scoped, source_preparation)
    context, optional = local_context(upstream, graph, set(nodes))
    compact_call_context(context, optional)
    supplied = {**optional, **artifacts, 'upstream-context':context}
    mandatory = ['upstream-context'] + [key for key in artifacts
        if not key.startswith(('extract:', 'spec:'))]
    if role == 'common':
        supplied['needs-summary'] = needs_summary(nodes, artifacts)
        mandatory.append('needs-summary')
        ranges = []
    else:
        mandatory.extend('spec:' + ident for ident in nodes)
        ranges = [dict(n['source']) for n in nodes.values()]
        # Candidate evidence is exactly the support for the judgments under review.
        # Never recursively expand optional extraction reports or caller context.
        ranges.extend(source_ranges(artifacts.get('candidate', {})))
    if scoped is not None:
        mapped = [x['original'] for _,m in scoped for x in m['mappings']]
        unavailable = []
        for edge in context['call_requirements']:
            detail = optional[edge['full_context']]
            for field in ('callsite', 'callsites'):
                for source in source_ranges(detail.get(field)):
                    if not any(m['path'] == source['path'] and m['start'] <= source['start']
                               and source['end'] <= m['end'] for m in mapped):
                        unavailable.append(source)
        context['unavailable_callsite_sources'] = unavailable
        # The manifest is an allowlist, not a mandatory reading list. Missing cited
        # ranges still fail in BundleReader; no original-repository fallback.
        mandatory = ['source-index'] + [x for x in mandatory if x != 'source-index']
    return supplied, ([{'tool':'artifact', 'id':i} for i in dict.fromkeys(mandatory)]
                      + read_actions(ranges))


def prepare_legacy(role, graph, nodes, upstream, artifacts, scoped=None, source_preparation=None):
    selected = set(nodes)
    context, optional = local_context(upstream, graph, selected)
    supplied = {**optional, **artifacts, "upstream-context":context}
    mandatory = ["upstream-context"] + list(artifacts)
    if "source-index" in supplied:
        mandatory = ["source-index"] + [x for x in mandatory if x != "source-index"]
    ranges = [dict(n["source"]) for n in nodes.values()]
    if source_preparation is not None and scoped is None:
        prepared = source_preparation.prepare(list(nodes.values()))
        ranges.extend({k:x[k] for k in ("path","start","end")} for x in prepared["source_fragments"])
        from stage3.read_materials import compact_preparation
        supplied["source-preparation"] = compact_preparation(prepared, include_text=False)
        mandatory.append("source-preparation")
    # Original callsite coordinates, never the derived excerpt strings.
    for edge in context["call_requirements"]:
        ranges.extend(source_ranges(edge.get("callsites",[])))
        if edge.get("callsite"):
            ranges.extend(source_ranges(edge["callsite"]))
    if role in ("common","review"):
        for key, artifact in artifacts.items():
            if key.startswith("extract:") or key == "candidate":
                ranges.extend(source_ranges(artifact))
    if scoped is not None:
        # Callsite context outside this bundle stays an explicit unavailable background.
        mapped = [x["original"] for _,m in scoped for x in m["mappings"]]
        context["unavailable_callsite_sources"] = [x for x in ranges if not any(
            m["path"] == x["path"] and m["start"] <= x["start"] <= x["end"] <= m["end"]
            for m in mapped)]
        ranges = list(mapped)
        # Review/planning citations remain mandatory; missing cited source must block.
        if role in ("common","review"):
            for key, artifact in artifacts.items():
                if key.startswith("extract:") or key == "candidate":
                    ranges.extend(source_ranges(artifact))
    actions = [{"tool":"artifact","id":i} for i in dict.fromkeys(mandatory)]
    actions += read_actions(ranges)
    return supplied, actions

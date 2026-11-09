"""Explicit, unresolved dependency hypotheses; never source or graph exemptions."""
from stage1.contracts import safe_id, nonempty


def catalog(spec, extraction):
    return {source: value for source, value in (
        ('material_requests', spec.get('material_requests', [])),
        ('spec_unknowns', spec.get('unknowns', [])),
        ('extraction_unknowns', extraction.get('unknowns', [])))}


def inspect(spec, extraction, graph, ident):
    assumptions=spec.get('conditional_assumptions', [])
    if not isinstance(assumptions,list):return ['conditional_assumptions must be a list'],set()
    errors=[]; covered=set(); ids=set(); gaps=catalog(spec,extraction)
    symbols={graph['nodes'][e['callee']]['symbol'] for e in graph['edges'].values()
             if e['caller']==ident and e.get('callee') in graph['nodes'] and e.get('certainty')!='unresolved'}
    claims={c.get('id'):c for c in spec.get('claims',[]) if isinstance(c,dict)}
    for a in assumptions:
        before=len(errors)
        if not isinstance(a,dict):errors.append('conditional assumption must be an object');continue
        if not safe_id(a.get('id')) or a['id'] in ids:errors.append('unique conditional assumption ID required')
        if isinstance(a.get('id'),str):ids.add(a['id'])
        if not isinstance(a.get('symbol'),str) or a['symbol'] not in symbols:errors.append('conditional assumption must name a resolved outgoing dependency')
        if not nonempty(a.get('condition')) or a['condition'] not in spec.get('sections',{}).get('environment',''):
            errors.append('condition must quote actual sections.environment text')
        if not nonempty(a.get('explanation')):errors.append('conditional assumption explanation required')
        affected=a.get('affected_claim_ids')
        if not isinstance(affected,list) or not affected or any(not isinstance(i,str) or i not in claims or claims[i].get('kind')=='source_fact' for i in affected):
            errors.append('affected_claim_ids must identify conditional candidate/interpretation claims')
        refs=a.get('gaps'); pending=set()
        if not isinstance(refs,list) or not refs:errors.append('conditional assumption requires exact gap references');continue
        for ref in refs:
            if not isinstance(ref,dict) or not isinstance(ref.get('source'),str) or ref.get('source') not in gaps or type(ref.get('index')) is not int:
                errors.append('invalid conditional gap reference');continue
            source,index=ref['source'],ref['index']
            if not isinstance(gaps[source],list):errors.append('gap source must be a list');continue
            if not 0<=index<len(gaps[source]):errors.append('conditional gap index out of range');continue
            gap=gaps[source][index]
            if not isinstance(gap,dict):errors.append('gap must be an object');continue
            if gap.get('symbol')!=a.get('symbol') or gap.get('category')!='dependency_contract':
                errors.append('only explicitly classified dependency contracts may be conditional')
            if (source,index) in covered or (source,index) in pending:errors.append('duplicate conditional gap reference')
            pending.add((source,index))
        if len(errors)==before:covered.update(pending)
    return errors,covered


def review_checks(report, assumptions):
    if not assumptions:return []
    checks=report.get('assumption_checks'); errors=[]
    if not isinstance(checks,list):return ['assumption_checks required for every conditional assumption']
    expected={a['id'] for a in assumptions}; seen=set()
    for check in checks:
        if not isinstance(check,dict):errors.append('assumption check must be an object');continue
        ident=check.get('id')
        if not isinstance(ident,str) or ident not in expected or ident in seen:errors.append('invalid or duplicate assumption check ID')
        else:seen.add(ident)
        if check.get('decision') not in ('acceptable_condition','reject','unknown') or not nonempty(check.get('explanation')):
            errors.append('assumption check needs decision and explanation')
        if report.get('verdict')=='pass' and check.get('decision')!='acceptable_condition':errors.append('unaccepted assumption cannot pass')
    if seen!=expected:errors.append('every conditional assumption must be independently checked')
    return errors

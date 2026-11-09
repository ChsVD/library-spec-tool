"""Structural and evidence gates; semantic correctness remains a review obligation."""
import json
from stage1.contracts import safe_id, nonempty, check_evidence

SECTIONS = ('meaning', 'environment', 'preconditions', 'postconditions', 'effects', 'boundaries')
CHECKS = ('strength', 'preconditions', 'boundaries', 'representation', 'call_requirements', 'evidence', 'tool_support')


def base(report, reader, ident):
    if not isinstance(report, dict): return ['report must be an object']
    errors = []
    if report.get('function_id') != ident: errors.append('function_id differs from assignment')
    if len(json.dumps(report, ensure_ascii=False)) > 18000: errors.append('report exceeds 18000 characters; keep one function per report')
    return errors


def unknowns(report):
    value = report.get('unknowns')
    if not isinstance(value, list): return ['unknowns list required']
    return ['unknown requires description and blocking boolean' for x in value
            if not isinstance(x, dict) or not nonempty(x.get('description')) or type(x.get('blocking')) is not bool]


def discovery(report, reader, reads, *, node, known):
    errors = base(report, reader, node['id'])
    if not isinstance(report, dict): return errors
    errors += check_evidence([node['source']], reader) + unknowns(report)
    cov = report.get('coverage', {})
    if cov.get('outgoing') not in ('checked_scope', 'unknown') or not nonempty(cov.get('incoming')):
        errors.append('coverage needs outgoing=checked_scope/unknown and explicit incoming search limits')
    neighbors = report.get('neighbors')
    edges = report.get('edges')
    if not isinstance(neighbors, list) or not isinstance(edges, list): return errors+['neighbors and edges lists required']
    identities = dict(known)
    seen = set()
    for n in neighbors:
        if not isinstance(n, dict) or not safe_id(n.get('id')) or n['id'] in seen:
            errors.append('unique safe neighbor IDs required'); continue
        seen.add(n['id'])
        if not nonempty(n.get('symbol')) or not nonempty(n.get('configuration')):
            errors.append('neighbor symbol/configuration required')
        if n['id'] in identities and any(n.get(k)!=identities[n['id']].get(k) for k in ('symbol','source','configuration')):
            errors.append('conflicting known function identity')
        for key,other in known.items():
            if key!=n['id'] and other.get('symbol')==n.get('symbol') and other.get('source')==n.get('source'):
                errors.append('duplicate definition identity; reuse canonical ID: '+key)
        identities[n['id']] = n
        errors += check_evidence([n.get('source')], reader)
    seen = set()
    for e in edges:
        if not isinstance(e, dict) or not safe_id(e.get('id')) or e['id'] in seen:
            errors.append('unique safe edge IDs required'); continue
        seen.add(e['id'])
        if e.get('caller') not in identities or (e.get('callee') is not None and e.get('callee') not in identities):
            errors.append('edge endpoint absent')
        if node['id'] not in (e.get('caller'),e.get('callee')): errors.append('only incident edges allowed')
        if e.get('callee') is None and not nonempty(e.get('unresolved_target')): errors.append('unresolved callee requires target description')
        if e.get('certainty') not in ('direct','conditional','unresolved') or not nonempty(e.get('condition')):
            errors.append('edge certainty and condition required')
        errors += check_evidence([e.get('callsite')], reader)
        caller = identities.get(e.get('caller'), {}).get('source', {})
        site = e.get('callsite', {})
        if caller.get('path') != site.get('path') or not caller.get('start',0)<=site.get('start',-1)<=site.get('end',-1)<=caller.get('end',-2):
            errors.append('callsite must lie within caller source interval')
    return errors


def specification(report, reader, reads, *, node, graph):
    errors = base(report, reader, node['id'])
    if not isinstance(report, dict): return errors
    errors += check_evidence([node['source']], reader) + unknowns(report)
    if node.get('materials') and not any(x.startswith('material:'+node['materials'][0]+':') for x in reads):
        errors.append('writer must inspect the assigned primary module material')
    if report.get('proof_status') != 'not_proved': errors.append('proof_status must be not_proved')
    for field in SECTIONS:
        if not nonempty(report.get('sections', {}).get(field)): errors.append('missing section '+field)
    claims = report.get('claims')
    if not isinstance(claims,list) or not claims: return errors+['nonempty claims required']
    ids = set()
    for c in claims:
        if not isinstance(c,dict): errors.append('claim object required'); continue
        if not safe_id(c.get('id')) or c['id'] in ids: errors.append('unique claim IDs required')
        ids.add(c.get('id'))
        if c.get('kind') not in ('source_fact','interpretation','candidate') or not nonempty(c.get('text')):
            errors.append('claim kind/text required')
        errors += check_evidence(c.get('evidence'),reader,required=c.get('kind')!='candidate')
    uses = report.get('reference_uses')
    if not isinstance(uses,list): errors.append('reference_uses list required')
    else:
        for u in uses:
            if not isinstance(u,dict): errors.append('reference use object required'); continue
            if not all(nonempty(u.get(k)) for k in ('adaptation','limitations')): errors.append('reference adaptation/limitations required')
            errors += check_evidence(u.get('evidence'),reader)
    needs = report.get('common_needs')
    if not isinstance(needs,list): errors.append('common_needs list required')
    else:
        for n in needs:
            if not isinstance(n,dict) or n.get('status')!='needed_not_proved' or not all(nonempty(n.get(k)) for k in ('name','purpose')):
                errors.append('common need requires name/purpose and needed_not_proved')
    scenarios=report.get('caller_scenarios',[])
    incoming={k for k,e in graph['edges'].items() if e['callee']==node['id']}
    if not isinstance(scenarios,list): errors.append('caller_scenarios must be a list')
    else:
        for item in scenarios:
            if not isinstance(item,dict): errors.append('caller scenario object required'); continue
            if item.get('edge_id') not in incoming: errors.append('caller_scenarios must reference incoming edges')
            if item.get('status')!='inferred_usage_not_guaranteed' or not all(nonempty(item.get(k)) for k in ('provided_conditions','needed_guarantees')):
                errors.append('caller scenario needs separate conditions/guarantees and inferred_usage_not_guaranteed')
            errors += check_evidence(item.get('evidence'),reader)
    reqs = report.get('call_requirements')
    if not isinstance(reqs,list): return errors+['call_requirements list required']
    outgoing = {k for k,e in graph['edges'].items() if e['caller']==node['id']}
    observed = set()
    for r in reqs:
        if not isinstance(r,dict): errors.append('requirement object required'); continue
        if r.get('edge_id') not in outgoing: errors.append('requirement must reference an outgoing callsite')
        observed.add(r.get('edge_id'))
        if r.get('status')!='required_not_guaranteed' or not all(nonempty(r.get(k)) for k in ('precondition','postcondition')):
            errors.append('requirement needs scenario pre/post and required_not_guaranteed')
        errors += check_evidence(r.get('evidence'),reader)
    if observed != outgoing: errors.append('every known outgoing callsite needs a requirement or explicit unknown in its text')
    return errors


def all_evidence(spec):
    return [e for k in ('claims','reference_uses','call_requirements','caller_scenarios') for item in spec.get(k,[]) for e in item['evidence']]


def review(report, reader, reads, *, node, spec, graph):
    errors = base(report,reader,node['id'])
    if not isinstance(report,dict): return errors
    if 'candidate' not in reads: errors.append('review must inspect candidate artifact')
    adjacent={x for e in graph['edges'].values() if node['id'] in (e['caller'],e['callee'])
              for x in (e['caller'],e['callee']) if x and x!=node['id']}
    for ident in adjacent:
        if graph['nodes'][ident]['spec'] and 'neighbor:'+ident not in reads:
            errors.append('review must inspect current neighbor candidate: '+ident)
    errors += check_evidence([node['source']],reader)
    errors += check_evidence(report.get('evidence'),reader)
    if report.get('verdict') not in ('pass','needs_revision','insufficient','tool_blocked'): errors.append('invalid review verdict')
    for k in CHECKS:
        if not nonempty(report.get('checks',{}).get(k)): errors.append('review check missing: '+k)
    findings = report.get('findings')
    if not isinstance(findings,list): return errors+['findings list required']
    for f in findings:
        if not isinstance(f,dict) or not nonempty(f.get('description')) or type(f.get('blocking')) is not bool:
            errors.append('finding description/blocking required')
        elif f['blocking'] and report.get('verdict')=='pass': errors.append('pass cannot contain blocking findings')
    if report.get('verdict')=='tool_blocked':
        errors += check_evidence(report.get('tool_evidence'),reader)
    if report.get('verdict')=='pass':
        discovered=graph.get('discoveries',{}).get(node['id'],{})
        if discovered.get('coverage',{}).get('outgoing')=='unknown':
            errors.append('unresolved outgoing graph coverage cannot pass')
        resolutions=report.get('discovery_resolutions',[])
        if not isinstance(resolutions,list): errors.append('discovery_resolutions must be a list'); resolutions=[]
        resolved=set()
        for r in resolutions:
            if not isinstance(r,dict) or type(r.get('index')) is not int or not nonempty(r.get('explanation')):
                errors.append('discovery resolution needs index and explanation'); continue
            i=r['index']
            if not 0<=i<len(discovered.get('unknowns',[])) or i in resolved:
                errors.append('invalid or duplicate discovery resolution index'); continue
            if r.get('handling')=='conditional_scope':
                condition=r.get('condition')
                if not nonempty(condition) or condition not in spec['sections']['environment']:
                    errors.append('conditional resolution must quote an actual candidate environment condition')
                else: resolved.add(i)
            elif r.get('handling')=='resolved':
                evidence_errors=check_evidence(r.get('evidence'),reader)
                errors+=evidence_errors
                if not evidence_errors: resolved.add(i)
            else: errors.append('discovery blocker remains unresolved')
        for i,u in enumerate(discovered.get('unknowns',[])):
            if u.get('blocking') and i not in resolved:
                errors.append('blocking discovery needs explicit evidence or conditional scope resolution: '+str(i))
        errors += check_evidence(all_evidence(spec), reader, required=False)
        errors += check_evidence([e['callsite'] for e in graph['edges'].values()
                                 if node['id'] in (e['caller'],e['callee'])],reader,required=False)
        if any(u['blocking'] for u in spec['unknowns']): errors.append('blocking unknown cannot pass')
    return errors

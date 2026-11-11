"""Evidence and coverage gates; semantic validity requires independent review."""
import json
from . import planning
from stage1.contracts import check_evidence, nonempty, safe_id

CATEGORIES = ('mathematical_model', 'representation', 'word_size', 'array_length',
              'capacity', 'memory_aliasing', 'range_conversion', 'arithmetic', 'invariant', 'failure_state')
CHECKS = ('coverage', 'strength', 'assumptions', 'representation', 'dependencies',
          'reference_adaptation', 'counterexamples', 'spec_compatibility')
REFERENCE_CHECKS = ('source_accuracy', 'premises_representation',
                    'use_differences', 'target_unvalidated')


def base(report, max_report_chars=24000):
    if not isinstance(report, dict): return ['report object required']
    errors=[]
    if 'protocol_version' in report and (type(report['protocol_version']) is not int or report['protocol_version'] not in (2, 3)):
        errors.append('unsupported protocol_version')
    if max_report_chars is not None and len(json.dumps(report,ensure_ascii=False))>max_report_chars: errors.append(f'report exceeds {max_report_chars} characters')
    if report.get('proof_status')!='not_proved':errors.append('proof_status must be not_proved')
    return errors


def extraction_v3(report, reader, reads, *, node, max_report_chars=24000):
    errors = base(report, max_report_chars)
    if report.get('function_id') != node['id']: errors.append('wrong function')
    if 'spec' not in reads: errors.append('must inspect spec')
    errors += check_evidence([node['source']], reader)
    if node.get('status') == 'reference_draft' and 'upstream-context' not in reads:
        errors.append('must inspect reference upstream context')
    if not nonempty(report.get('analysis')): errors.append('analysis required')
    needs = report.get('needs')
    if not isinstance(needs, list): return errors + ['needs list required']
    errors += planning.requirements(report)
    upstream = node['spec'].get('common_needs', [])
    expected = {'present': 'common_needs' in node['spec'], 'items': upstream,
                'ids': ['upstream-' + str(i) for i in range(len(upstream))]}
    if 'upstream_needs' in report and report['upstream_needs'] != expected:
        errors.append('upstream_needs must exactly retain program supplied provenance')
    for need in needs:
        if not isinstance(need, dict): continue
        if need.get('function_id') != node['id']: errors.append('need function_id mismatch')
        if need.get('source') == 'upstream' and need.get('upstream_need_id') not in expected['ids']:
            errors.append('upstream need must identify existing upstream_need_id')
        errors += check_evidence(need.get('evidence'), reader)
    return errors


def candidate_v3(report, reader, reads, *, nodes, extracts, max_report_chars=24000):
    errors = base(report, max_report_chars) + check_upstream_conditions(report, nodes)
    if any(n.get('status') == 'reference_draft' for n in nodes.values()) and 'upstream-context' not in reads:
        errors.append('must inspect reference upstream context')
    if 'needs-summary' not in reads:
        errors.append('must inspect program-generated needs-summary')
    errors += planning.records(report, reader)
    expected = {(ident, need) for ident, node in nodes.items()
                for need in planning.common_need_ids(node, extracts[ident])}
    seen = set()
    for use in report.get('uses', []) if isinstance(report.get('uses'), list) else []:
        if not isinstance(use, dict): continue
        f, need = use.get('function_id'), use.get('need_id')
        if not isinstance(f, str) or not isinstance(need, str): continue
        key = (f, need)
        if key not in expected: errors.append('use identifies unknown function/need: ' + str(key))
        if key in seen: errors.append('each function/need requires exactly one use record')
        seen.add(key)
    if seen != expected: errors.append('uses must cover every original and extracted need')
    return errors


def review_v3(report, reader, reads, *, proposal, nodes, max_report_chars=24000):
    from .components import validate_v3
    errors = base(report, max_report_chars)
    if not isinstance(report, dict): return errors
    if report.get('protocol_version') != 3: errors.append('review protocol_version must match candidate version 3')
    if report.get('candidate_digest') != planning.candidate_digest(proposal):
        errors.append('candidate_digest must match the exact reviewed candidate')
    if 'candidate' not in reads: errors.append('must inspect candidate')
    errors += check_upstream_conditions(proposal, nodes)
    for ident, node in nodes.items():
        if 'spec:' + ident not in reads: errors.append('must inspect each original spec')
        errors += check_evidence([node['source']], reader)
    if any(n.get('status') == 'reference_draft' for n in nodes.values()) and 'upstream-context' not in reads:
        errors.append('must inspect reference upstream context')
    expected = {(f, row['id']) for f, rows in upstream_conditions(nodes).items() for row in rows}
    seen = set()
    conditions = report.get('upstream_condition_checks', [])
    if not isinstance(conditions, list): errors.append('upstream_condition_checks list required'); conditions = []
    for condition in conditions:
        if not isinstance(condition, dict): errors.append('condition check object required'); continue
        f, ident = condition.get('function_id'), condition.get('assumption_id')
        if not isinstance(f, str) or not isinstance(ident, str): errors.append('invalid condition identity'); continue
        key = (f, ident)
        if key not in expected or key in seen: errors.append('unknown or duplicate condition check')
        seen.add(key)
        if condition.get('decision') not in ('preserved', 'needs_revision', 'unknown') or not nonempty(condition.get('explanation')):
            errors.append('condition check needs decision and explanation')
        if report.get('verdict') == 'pass' and condition.get('decision') != 'preserved':
            errors.append('unpreserved upstream condition cannot pass')
    if seen != expected: errors.append('review every upstream condition explicitly')
    if report.get('verdict') not in ('pass', 'partial', 'needs_revision', 'insufficient', 'tool_blocked'):
        errors.append('invalid verdict')
    checks = report.get('checks')
    for key in REFERENCE_CHECKS:
        if not isinstance(checks, dict) or not nonempty(checks.get(key)): errors.append('missing check: ' + key)
    errors += check_evidence(report.get('evidence'), reader)
    if report.get('verdict') == 'tool_blocked': errors += check_evidence(report.get('tool_evidence'), reader)
    errors += validate_v3(report, proposal)
    # Only accepted claims require the independent reviewer to have received their
    # source intervals. A missing source can instead be an insufficient judgment.
    accepted_refs = {r.get('reference_id') for r in report.get('reference_reviews', [])
                     if isinstance(r, dict) and isinstance(r.get('reference_id'), str) and r.get('verdict') == 'pass'} if isinstance(report.get('reference_reviews'), list) else set()
    for ref in proposal.get('references', []):
        if ref['id'] in accepted_refs: errors += check_evidence(ref.get('evidence'), reader)
    accepted_uses = {r.get('use_id') for r in report.get('use_reviews', [])
                     if isinstance(r, dict) and isinstance(r.get('use_id'), str) and r.get('verdict') == 'pass'} if isinstance(report.get('use_reviews'), list) else set()
    for use in proposal.get('uses', []):
        if use['id'] in accepted_uses:
            errors += check_evidence(use.get('search_evidence', []), reader, required=use.get('result') == 'not_found')
    if report.get('verdict') in ('pass', 'partial'):
        # Review must independently inspect any exported rule and its proof.
        from .strategies import validate
        accepted_rules = [row for row in proposal.get('reference_strategies', [])
                          if all(ident in accepted_refs for ident in row.get('reference_ids', []))]
        errors += validate(dict(proposal, reference_strategies=accepted_rules), reader)
    return errors


def upstream_conditions(nodes):
    """Immutable candidate scope; a reviewed assumption is still not a guarantee."""
    conditions={}
    for ident,node in nodes.items():
        rows=[{'id':a['id'],'condition':a['condition']}
              for a in node['spec'].get('conditional_assumptions',[])]
        if node.get('status')=='reference_draft':
            # Keep the entire original text, even "no new assumptions".
            rows.append({'id':'reference-assumptions','condition':node['spec']['assumptions']})
        if rows:conditions[ident]=rows
    return conditions



def check_upstream_conditions(report,nodes):
    expected=upstream_conditions(nodes)
    if report.get('upstream_conditions',{})!=expected:
        return ['upstream_conditions must exactly retain upstream assumption IDs and conditions']
    return []


def extraction(report, reader, reads, *, node, max_report_chars=24000):
    if isinstance(report, dict) and report.get('protocol_version') == 3:
        return extraction_v3(report, reader, reads, node=node, max_report_chars=max_report_chars)
    errors=base(report,max_report_chars)
    if not isinstance(report,dict):return errors
    if report.get('function_id')!=node['id']:errors.append('wrong function')
    if 'spec' not in reads:errors.append('must inspect spec')
    if node.get('status')=='reference_draft' and 'upstream-context' not in reads:
        errors.append('must inspect reference upstream context')
    errors+=check_evidence([node['source']],reader)
    if not nonempty(report.get('analysis')):errors.append('analysis required')
    categories=report.get('categories',{})
    for k in categories if isinstance(categories,dict) else []:
        v=categories.get(k,{}) if isinstance(categories,dict) else {}
        if not isinstance(v,dict) or v.get('status') not in ('needed','not_applicable','unknown') or not nonempty(v.get('reason')):
            errors.append('category status/reason required: '+k)
    if not isinstance(categories,dict):errors.append('categories must be an object when supplied')
    needs=report.get('needs')
    if not isinstance(needs,list):return errors+['needs list required']
    for n in needs:
        if not isinstance(n,dict) or not all(nonempty(n.get(k)) for k in ('name','purpose','proposed_statement','assumptions')):
            errors.append('need requires name, purpose, proposed_statement, assumptions');continue
        errors+=check_evidence(n.get('evidence'),reader)
    errors+=planning.requirements(report)
    return errors


def candidate(report, reader, reads, *, nodes, extracts, max_report_chars=24000):
    if isinstance(report, dict) and report.get('protocol_version') == 3:
        return candidate_v3(report, reader, reads, nodes=nodes, extracts=extracts, max_report_chars=max_report_chars)
    errors=base(report,max_report_chars)
    if not isinstance(report,dict):return errors
    errors+=check_upstream_conditions(report,nodes)
    if any(n.get('status')=='reference_draft' for n in nodes.values()) and 'upstream-context' not in reads:
        errors.append('must inspect reference upstream context')
    for ident in nodes:
        if 'extract:'+ident not in reads:errors.append('must inspect extraction: '+ident)
        if 'spec:'+ident not in reads:errors.append('must inspect spec: '+ident)
    items=report.get('items')
    if not isinstance(items,list):return errors+['items list required']
    ids=set()
    for item in items:
        if not isinstance(item,dict):errors.append('item object required');continue
        ident=item.get('id')
        if not safe_id(ident) or ident in ids:errors.append('unique safe item IDs required')
        if isinstance(ident,str):ids.add(ident)
        if item.get('kind') not in ('definition','representation','lemma','invariant','predicate'):errors.append('invalid kind')
        if item.get('proof_status')!='not_proved':errors.append('items remain not_proved')
        for key in ('name','parameters','assumptions','statement','purpose','adaptation','validation_plan'):
            if not nonempty(item.get(key)):errors.append('item field required: '+key)
        if item.get('origin') not in ('source_fact','adapted','new_candidate'):errors.append('origin required')
        errors+=check_evidence(item.get('evidence'),reader,required=item.get('origin')!='new_candidate')
        errors+=planning.obligations(item,reader)
        used=item.get('used_by')
        if not isinstance(used,list) or not used or any(not isinstance(x,str) or x not in nodes for x in used):errors.append('used_by must reference selected functions')
    for item in items:
        if not isinstance(item,dict):continue
        deps=item.get('depends_on')
        if not isinstance(deps,list) or any(not isinstance(x,str) or x not in ids or x==item.get('id') for x in deps):errors.append('dependency missing or self-reference')
    # Definition/lemma dependency cycles are not accepted as established mutual facts.
    edges={i['id']:i.get('depends_on',[]) for i in items if isinstance(i,dict) and isinstance(i.get('id'),str)}
    def cyclic(key,stack):
        if key in stack:return True
        return any(cyclic(d,stack|{key}) for d in edges.get(key,[]) if isinstance(d,str))
    if not errors and any(cyclic(k,set()) for k in edges):errors.append('cyclic common-content dependencies')
    coverage=report.get('coverage',{})
    if not isinstance(coverage,dict) or set(coverage)!=set(nodes):return errors+['coverage must include every selected function exactly once']
    for ident,node in nodes.items():
        row=coverage[ident]
        if not isinstance(row,dict):errors.append('coverage row object required');continue
        needed=list(node['spec'].get('common_needs',[]))+list(extracts[ident]['needs'])
        mappings=row.get('needs')
        if not isinstance(mappings,list) or len(mappings)!=len(needed):errors.append('map every original and extracted need');continue
        for index,m in enumerate(mappings):
            if not isinstance(m,dict) or m.get('index')!=index:errors.append('need indices must be ordered and complete');continue
            mapped=m.get('item_ids')
            if not isinstance(mapped,list) or any(not isinstance(x,str) or x not in ids for x in mapped):errors.append('need maps to unknown item')
            if isinstance(mapped,list) and not errors:
                for key in mapped:
                    if isinstance(key,str) and key in ids and ident not in next(i for i in items if i['id']==key)['used_by']:
                        errors.append('mapped need missing function in used_by')
            if not nonempty(m.get('explanation')):errors.append('need mapping explanation required')
            if not mapped and m.get('action')!='not_needed' and not nonempty(m.get('unresolved')):errors.append('unmapped need must remain unresolved')
        cats=row.get('categories',{})
        if not isinstance(cats,dict):errors.append('coverage categories must be an object')
        for k in cats if isinstance(cats,dict) else []:
            c=cats.get(k,{}) if isinstance(cats,dict) else {}
            if not isinstance(c,dict) or c.get('status') not in ('covered','not_applicable','unresolved') or not nonempty(c.get('reason')):
                errors.append('coverage category required: '+k);continue
            refs=c.get('item_ids')
            if not isinstance(refs,list) or any(not isinstance(x,str) or x not in ids for x in refs) or (c['status']=='covered' and not refs):errors.append('category item mapping invalid')
    errors+=planning.records(report,reader)
    unknown=report.get('unknowns')
    if not isinstance(unknown,list) or any(not isinstance(u,dict) or not nonempty(u.get('description')) or type(u.get('blocking')) is not bool for u in unknown):errors.append('unknowns with blocking boolean required')
    return errors


def review(report, reader, reads, *, proposal, nodes, max_report_chars=24000, component_review=False):
    if isinstance(proposal, dict) and proposal.get('protocol_version') == 3:
        return review_v3(report, reader, reads, proposal=proposal, nodes=nodes, max_report_chars=max_report_chars)
    errors=base(report,max_report_chars)
    if not isinstance(report,dict):return errors
    if 'candidate' not in reads:errors.append('must inspect candidate')
    errors+=check_upstream_conditions(proposal,nodes)
    if any(n.get('status')=='reference_draft' for n in nodes.values()) and 'upstream-context' not in reads:
        errors.append('must inspect reference upstream context')
    expected={(f,a['id']) for f,items in upstream_conditions(nodes).items() for a in items}
    if expected:
        assessments=report.get('upstream_condition_checks',[])
        seen=set()
        if not isinstance(assessments,list):
            errors.append('upstream_condition_checks must be a list'); assessments=[]
        for item in assessments:
            if not isinstance(item,dict):
                errors.append('invalid upstream condition check'); continue
            f=item.get('function_id'); a=item.get('assumption_id')
            if not isinstance(f,str) or not isinstance(a,str):
                errors.append('invalid upstream condition identity'); continue
            key=(f,a)
            if key not in expected or key in seen:errors.append('unknown or duplicate upstream condition check')
            seen.add(key)
            if item.get('decision') not in ('preserved','needs_revision','unknown') or not nonempty(item.get('explanation')):
                errors.append('condition check needs decision and explanation')
            if report.get('verdict')=='pass' and item.get('decision')!='preserved':
                errors.append('unpreserved upstream condition cannot pass')
        if seen!=expected:errors.append('review every upstream condition explicitly')
    for ident,node in nodes.items():
        if 'spec:'+ident not in reads:errors.append('must inspect each original spec')
        errors+=check_evidence([node['source']],reader)
    errors+=check_evidence(report.get('evidence'),reader)
    verdict=report.get('verdict')
    if verdict not in ('pass','needs_revision','insufficient','tool_blocked') + (('partial',) if component_review else ()):errors.append('invalid verdict')
    checks=report.get('checks',{})
    if not isinstance(checks,dict):checks={}
    for k in CHECKS:
        if not nonempty(checks.get(k)):errors.append('missing check: '+k)
    findings=report.get('findings')
    if not isinstance(findings,list):return errors+['findings list required']
    for f in findings:
        if not isinstance(f,dict) or not nonempty(f.get('description')) or type(f.get('blocking')) is not bool:errors.append('invalid finding')
        elif verdict=='pass' and f['blocking']:errors.append('blocking finding cannot pass')
    if verdict=='tool_blocked':errors+=check_evidence(report.get('tool_evidence'),reader)
    if component_review:
        from .components import validate as component_validate
        errors+=component_validate(report,proposal)
    if verdict in ('pass','partial'):
        errors+=planning.records(proposal,reader)
        for item in proposal['items']:errors+=planning.obligations(item,reader)
        for i in proposal['items']:errors+=check_evidence(i['evidence'],reader,required=False)
    if verdict=='pass':
        if any(u['blocking'] for u in proposal['unknowns']):errors.append('blocking unknown cannot pass')
        for row in proposal['coverage'].values():
            if any(n.get('unresolved') for n in row['needs']) or any(c['status']=='unresolved' for c in row.get('categories',{}).values()):errors.append('unresolved coverage cannot pass')
    return errors

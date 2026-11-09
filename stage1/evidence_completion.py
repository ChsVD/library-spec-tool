"""Plan bounded citation completion exclusively from extracted bundle contents."""
from .contracts import check_evidence


def citations(value):
    if isinstance(value,dict):
        if set(('path','start','end'))<=value.keys() and isinstance(value['path'],str) and type(value['start']) is int and type(value['end']) is int:
            yield {k:value[k] for k in ('path','start','end')}
        else:
            for item in value.values():yield from citations(item)
    elif isinstance(value,list):
        for item in value:yield from citations(item)


def plan(report,reader):
    if not hasattr(reader,'content'):
        return original_plan(report,reader)
    evidence=[];unavailable=[]
    for source in citations(report):
        if not check_evidence([source],reader):continue
        if not 1<=source['start']<=source['end']<=1000000:
            unavailable.append(source);continue
        content=getattr(reader,'content',{}).get(source['path'],{})
        if any(i not in content for i in range(source['start'],source['end']+1)):
            unavailable.append(source);continue
        evidence.append(source)
        for _,manifest in getattr(reader,'bundles',[]):
            for unit in manifest.get('macro_units',[]):
                body=unit['source']
                if body['path']==source['path'] and body['start']<=source['end'] and source['start']<=body['end']:
                    evidence.append(body)
                    evidence.extend(c['source'] for c in unit['conditions'])
    merged=[]
    for e in sorted(evidence,key=lambda x:(x['path'],x['start'],x['end'])):
        if merged and merged[-1]['path']==e['path'] and e['start']<=merged[-1]['end']+1:
            merged[-1]['end']=max(merged[-1]['end'],e['end'])
        else:merged.append(dict(e))
    actions=[]
    total=0
    for e in merged:
        intervals=[]
        for n in range(e['start'],e['end']+1):
            if not check_evidence([{'path':e['path'],'start':n,'end':n}],reader):continue
            if intervals and n==intervals[-1][1]+1:intervals[-1][1]=n
            else:intervals.append([n,n])
            total+=1
        actions.extend({'tool':'read','path':e['path'],'start':a,'count':b-a+1} for a,b in intervals)
    if total>80 or len(actions)>8:
        return [],unavailable+[{'reason':'bundle completion exceeds 80 lines or 8 actions'}]
    return actions,unavailable


def original_plan(report,reader,max_lines=80,max_actions=8):
    """Only missing original lines; planning does not credit a source read."""
    missing={};unavailable=[]
    for source in citations(report):
        if not check_evidence([source],reader):continue
        try:
            if not 1<=source['start']<=source['end'] or source['end']-source['start']>10000:
                raise ValueError('citation interval exceeds bounded completion')
            lines,sha=reader.lines(source['path'])
            if source['end']>len(lines):raise ValueError('citation exceeds original file')
            ranges=reader.reads.get(source['path'],[])
            needed={n for n in range(source['start'],source['end']+1)
                    if not any(a<=n<=b and digest==sha for a,b,digest in ranges)}
            missing.setdefault(source['path'],set()).update(needed)
            if sum(map(len,missing.values()))>max_lines:
                raise ValueError('missing evidence exceeds bounded completion')
        except (ValueError,OSError,UnicodeError,KeyError,TypeError) as exc:
            unavailable.append({**source,'reason':str(exc)})
    if unavailable:return [],unavailable
    actions=[]
    for path,numbers in sorted(missing.items()):
        intervals=[]
        for n in sorted(numbers):
            if intervals and n==intervals[-1][1]+1:intervals[-1][1]=n
            else:intervals.append([n,n])
        actions.extend({'tool':'read','path':path,'start':a,'count':b-a+1} for a,b in intervals)
    if len(actions)>max_actions:return [],[{'reason':'too many bounded evidence completion actions'}]
    return actions,[]


def citation_feedback(report, reader, max_chars=4000):
    """Describe a bounded overbroad citation without reading or editing any source.

    Only citations intersecting already delivered lines qualify. A wholly missing
    source belongs to material acquisition, not citation repair.
    """
    import json
    def intervals(numbers):
        result=[]
        for n in sorted(numbers):
            if result and n==result[-1][1]+1:result[-1][1]=n
            else:result.append([n,n])
        return result
    issues=[];seen=set();has_overlap=False
    for source in citations(report):
        key=(source['path'],source['start'],source['end'])
        if key in seen:continue
        seen.add(key)
        if len(seen)>64 or not 1<=source['start']<=source['end']<=1000000 or source['end']-source['start']>10000:return None
        if not check_evidence([source],reader):continue
        content=getattr(reader,'content',{}).get(source['path'],{})
        requested=set(range(source['start'],source['end']+1))
        available=requested.intersection(content)
        missing=requested-available
        if not missing:continue
        delivered={n for n in available if not check_evidence([{'path':source['path'],'start':n,'end':n}],reader)}
        has_overlap=has_overlap or bool(delivered)
        issues.append({'citation':source,'available_intervals':intervals(available),
                       'delivered_intervals':intervals(delivered),'missing_intervals':intervals(missing)})
        if len(issues)>16:return None
    if not issues or not has_overlap:return None
    feedback={'citation_judgment':issues,'instruction':
        'One bounded citation judgment. Intervals are original line numbers within each cited range, not new source. '
        'Decide whether your citation was overbroad or whether missing lines are needed to support the claim. '
        'If already delivered evidence fully supports it, return finish or patch_report with precise citations and a citation_judgment explanation. '
        'Do not silently remove obligations, weaken claims, assume missing lines are irrelevant, or cite merely available unread lines. '
        'If substantive evidence is missing or uncertain, return {"tool":"needs_material","reason":"..."}. '
        'No new reads or extra drafting turns in this repair. The complete report will be validated again; this is not semantic approval.'}
    return feedback if len(json.dumps(feedback,ensure_ascii=False))<=max_chars else None

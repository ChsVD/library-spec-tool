"""Build role-local mandatory delivery plans from the same evidence gates as validation."""
from .context_cards import compact_context,writer_context
from .contracts import all_evidence


def plan(node, graph, artifacts, *, review=False, candidate=None, bundles=()):
    view,_=compact_context(graph,node['id'],max_chars=10**9)
    ids=['source-index']
    if 'callee-contracts' in artifacts:ids.append('callee-contracts')
    if not review and 'dependency-gap-index' in artifacts:ids.append('dependency-gap-index')
    if node.get('materials'):
        prefix='material:'+node['materials'][0]+':'
        primary=sorted(k for k in artifacts if k.startswith(prefix))
        ids.extend(primary or [prefix+'1'])
    if review:
        ids.append('candidate')
        adjacent={x for e in graph['edges'].values() if node['id'] in (e['caller'],e['callee'])
                  for x in (e['caller'],e['callee']) if x and x!=node['id']}
        ids.extend('neighbor:'+i for i in sorted(adjacent) if graph['nodes'][i].get('spec'))
    if not review and 'writer-schema' in artifacts:
        ids.append('writer-schema')
        ids.extend(k for k in artifacts if k.startswith(('edges:'+node['id']+':','gaps:'+node['id']+':')))
    else:
        ids.extend(e['detail'] for e in view['edges'] if review or e['caller']==node['id'])
        ids.extend(u['detail'] for u in view['unknowns'])
    evidence=[node['source']]
    for e in graph['edges'].values():
        if e['caller']==node['id'] or (review and e['callee']==node['id']):
            evidence.append(e['callsite'])
        if e['caller']==node['id'] and e.get('macro_expansion'):
            evidence.append(e['macro_expansion']['callsite'])
    if review and candidate:evidence.extend(all_evidence(candidate))
    # Read whole extracted macro snippets, retaining guards and intervening lines.
    for _, manifest in bundles:
        evidence.extend(c['source'] for c in manifest['report'].get('callee_contracts',[]))
        for unit in manifest.get('macro_units',[]):
            evidence.extend(c['source'] for c in unit['conditions'])
        for snippet in manifest['report']['snippets']:
            if snippet['kind']=='macro':
                evidence.append(snippet['source'])
    ranges=[]
    for x in sorted(evidence,key=lambda e:(e['path'],e['start'],e['end'])):
        if ranges and ranges[-1]['path']==x['path'] and x['start']<=ranges[-1]['end']+1:
            ranges[-1]['end']=max(ranges[-1]['end'],x['end'])
        else:ranges.append(dict(x))
    actions=[{'tool':'artifact','id':key} for key in dict.fromkeys(ids)]
    for x in ranges:
        for start in range(x['start'],x['end']+1,80):
            actions.append({'tool':'read','path':x['path'],'start':start,'count':min(80,x['end']-start+1)})
    return actions

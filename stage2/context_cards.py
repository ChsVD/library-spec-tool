"""Compact navigation and lossless on-demand context cards; graph on disk is unchanged."""
import copy
import json
import json
from .graph import context, digest


def pages(items,prefix,cards,limit=3000):
    """Bounded pages with stable item keys; no record is silently truncated."""
    refs={};page={};number=1
    for key,value in items:
        if page and len(json.dumps({**page,key:value},ensure_ascii=False))>limit:
            cards[prefix+':'+str(number)]=page;page={};number+=1
        page[key]=value;refs[key]=prefix+':'+str(number)
    if page:cards[prefix+':'+str(number)]=page
    return refs


def ranges(manifest):
    result=[]
    for x in sorted((m['original'] for m in manifest['mappings']),key=lambda s:(s['path'],s['start'],s['end'])):
        if result and result[-1]['path']==x['path'] and x['start']<=result[-1]['end']+1:
            result[-1]['end']=max(result[-1]['end'],x['end'])
        else:result.append(dict(x))
    return result


def source_index(bundles):
    return [{'function_id':m['report']['function_id'],'source_kind':m.get('source_kind','original_extracted_copy'),'ranges':ranges(m),
             'coverage':m['report']['coverage'],
             'blocking_unknown_count':sum(bool(u['blocking']) for u in m['report']['unknowns']),
             'details':'bundle:'+m['report']['function_id']} for _,m in bundles]


def source_cards(bundles):
    cards={'source-index':source_index(bundles)}
    for _,m in bundles:
        ident=m['report']['function_id'];report=m['report'];definitions=[]
        for i,s in enumerate(report['snippets']):
            if s['kind']!='macro':continue
            # Same source/configuration has one definition card across all uses.
            key='macro:'+digest({k:s[k] for k in ('source','symbol','condition')})[:16]
            cards[key]={k:s[k] for k in ('source','symbol','condition')}
            definitions.append({'index':i,'symbol':s['symbol'],'detail':key})
        refs=pages([(str(i),u) for i,u in enumerate(report['unknowns'])],'gaps:'+ident,cards)
        unknowns=[{'index':i,'blocking':u['blocking'],'detail':refs[str(i)]} for i,u in enumerate(report['unknowns'])]
        cards['bundle:'+ident]={'configuration':m.get('configuration'),
            'macro_definitions':definitions,'unknowns':unknowns,
            'warning':'Navigation is derived, not original evidence. Read cited source intervals.'}
    return cards


def compact_context(graph,ident,max_chars=18000):
    projected=copy.deepcopy(graph);cards={};edge_details=[]
    for key,e in list(projected['edges'].items()):
        if ident not in (e['caller'],e['callee']):continue
        value=copy.deepcopy(e)
        if value.get('macro_expansion'):
            value.pop('condition',None);value.pop('unresolved_target',None)
        edge_details.append((key,value))
        projected['edges'][key]={k:e[k] for k in ('id','caller','callee','callsite','certainty')}
        projected['edges'][key]['kind']='macro_expansion' if e.get('macro_expansion') else 'direct'
    refs=pages(edge_details,'edges:'+ident,cards)
    for key,ref in refs.items():projected['edges'][key]['detail']=ref
    disc=projected['discoveries'].get(ident)
    if disc:
        refs=pages([(str(i),u) for i,u in enumerate(disc.get('unknowns',[]))],'gaps:'+ident,cards)
        disc['unknowns']=[{'index':i,'blocking':u['blocking'],'detail':refs[str(i)]} for i,u in enumerate(disc.get('unknowns',[]))]
    view=context(projected,ident,max_chars)
    view['navigation']='Read detail pages for edge conditions/requirements/macro-body locations and unknowns. Pages are keyed by edge ID or unknown index. Never infer omitted conditions.'
    return view,cards


def writer_context(graph,ident,max_chars=18000):
    """One lossless relation delivery; shared paths, conditions and macro bodies."""
    cards={};shared={'paths':{},'conditions':{},'expansions':{}};reverse={k:{} for k in shared}
    def intern(group,value):
        key=digest(value)
        if key not in reverse[group]:
            ref=group[0]+str(len(shared[group])+1)
            reverse[group][key]=ref;shared[group][ref]=copy.deepcopy(value)
        return reverse[group][key]
    def encode(value):
        if isinstance(value,list):return [encode(x) for x in value]
        if not isinstance(value,dict):return value
        result={}
        for k,v in value.items():
            if k in ('path','condition') and isinstance(v,str):
                result[k+'_ref']=intern('paths' if k=='path' else 'conditions',v)
            elif k=='macro_expansion':
                body={a:b for a,b in v.items() if a not in ('root_call_index','parent_expansion_index')}
                result['macro_use']={'definition_ref':intern('expansions',encode(body)),
                    'root_call_index':v.get('root_call_index'),'parent_expansion_index':v.get('parent_expansion_index')}
            else:result[k]=encode(v)
        return result
    edges=[(key,encode(e)) for key,e in graph['edges'].items() if e['caller']==ident]
    pages(edges,'edges:'+ident,cards)
    disc=graph['discoveries'].get(ident,{})
    pages([(str(i),u) for i,u in enumerate(disc.get('unknowns',[]))],'gaps:'+ident,cards)
    neighbors={e['callee'] for e in graph['edges'].values() if e['caller']==ident and e['callee']}
    cards['writer-schema']={'shared':shared,'neighbors':{i:encode({k:graph['nodes'][i][k] for k in ('symbol','source','configuration')}) for i in sorted(neighbors)},
        'encoding':'path_ref resolves shared.paths; condition_ref resolves shared.conditions. macro_use.definition_ref resolves shared.expansions; root/parent indices remain per use. Each edge ID is a separate obligation. Original graph stays on disk.'}
    node=graph['nodes'][ident]
    view={'function':{k:node[k] for k in ('id','symbol','source','configuration')},
          'relations':'Read all supplied edges pages using writer-schema; each ID remains distinct.',
          'coverage':disc.get('coverage',{}),'scope':'Only own implementation, direct calls and recorded macro dependencies.'}
    if len(json.dumps(view,ensure_ascii=False))>max_chars:raise ValueError('writer assignment exceeds local limit')
    return view,cards


def decode_writer_edges(cards):
    """Round-trip used by tests/audits; model gets the documented compact schema."""
    shared=cards['writer-schema']['shared']
    def decode(value):
        if isinstance(value,list):return [decode(x) for x in value]
        if not isinstance(value,dict):return value
        result={}
        for k,v in value.items():
            if k=='path_ref':result['path']=shared['paths'][v]
            elif k=='condition_ref':result['condition']=shared['conditions'][v]
            elif k=='macro_use':
                result['macro_expansion']={**decode(shared['expansions'][v['definition_ref']]),
                    'root_call_index':v['root_call_index'],'parent_expansion_index':v['parent_expansion_index']}
            else:result[k]=decode(v)
        return result
    return {key:decode(edge) for name,page in cards.items() if name.startswith('edges:') for key,edge in page.items()}

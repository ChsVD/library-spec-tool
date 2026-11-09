"""Independent source preparation, one editable C file per function, explicit review."""
from stage1.model_factory import ModelConfig, create_model, model_factory
import argparse
import copy
import hashlib
import json
import re
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import partial
from pathlib import Path
from stage1.reader import Reader
from stage1.runner import snapshot
from stage1.task import Budgets, run_task, write_json, write_text
from .graph import digest
from .inventory import mask_noncode, scan_c
from .pipeline import load_manifest, material_pages
from .source_bundle import extraction_prompt, validate_extraction
from .macro_units import locate
from .bundle_reader import verify_bundle


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def inside(root,name):
    if not isinstance(name,str) or Path(name).is_absolute() or '..' in Path(name).parts or '\\' in name:
        raise ValueError('invalid relative preparation path')
    path=(Path(root)/name).resolve(strict=True)
    if not path.is_relative_to(Path(root).resolve()):raise ValueError('preparation path escapes directory')
    return path


def load_contracts(path):
    path=Path(path).resolve(strict=True); records=json.loads(path.read_text())
    if not isinstance(records,list):raise ValueError('callee registry must be a list')
    loaded=[]; seen=set()
    for r in records:
        if not isinstance(r,dict) or not all(isinstance(r.get(k),str) and r[k].strip() for k in ('symbol','configuration','interface_file','sha256')):
            raise ValueError('callee needs symbol, configuration, interface_file, sha256')
        if r.get('status') not in ('reviewed','proved') or r.get('format')!='qcp':
            raise ValueError('callee interface requires processed QCP contract; no inferred substitute')
        d=r.get('declaration',{})
        if not isinstance(d,dict) or not isinstance(d.get('path'),str) or any(type(d.get(k)) is not int for k in ('start','end')) or not 1<=d['start']<=d['end']:
            raise ValueError('callee original declaration identity required')
        key=(r['symbol'],digest(d),r['configuration'])
        if key in seen:raise ValueError('duplicate callee interface identity')
        seen.add(key)
        f=inside(path.parent,r['interface_file'])
        if sha(f)!=r['sha256']:raise ValueError('callee interface hash changed')
        text=f.read_text(); code=mask_noncode(text).strip()
        if not code.endswith(';') or re.search(r'\b'+re.escape(r['symbol'])+r'\s*\(',code) is None or scan_c(text,'interface.c')[0]:
            raise ValueError('callee interface must contain its declaration, not a function implementation')
        if text.strip()==code:raise ValueError('callee interface must include its specification annotations')
        loaded.append({**r,'text':text})
    return loaded


def block(part,text):
    if '/* preparation:' in text:raise ValueError('reserved preparation marker in source')
    return '/* preparation:begin '+part+' */\n'+text.rstrip('\n')+'\n/* preparation:end '+part+' */\n'


def parse_parts(text):
    lines=text.splitlines(); parts={}; active=None
    for n,line in enumerate(lines,1):
        m=re.fullmatch(r'/\* preparation:(begin|end) ([a-z0-9_-]+) \*/',line)
        if not m:continue
        op,key=m.groups()
        if op=='begin':
            if active is not None or key in parts:raise ValueError('duplicate/nested preparation section')
            active=(key,n+1)
        else:
            if active is None or active[0]!=key or n<=active[1]:raise ValueError('invalid preparation section')
            parts[key]=(active[1],n-1);active=None
    if active or 'implementation' not in parts:raise ValueError('missing/unfinished implementation section')
    return lines,parts


def assemble(root,node,report,contracts):
    lines=['/* EDITABLE SOURCE PREPARATION. Review configuration, dependencies and interfaces before approval. */\n']
    records=[]; gaps=[]
    for i,s in enumerate(report['snippets']):
        if s['kind']=='reference':raise ValueError('standalone extraction must not collect reference or callee implementations')
        src=s['source']; raw=inside(root,src['path']).read_text().splitlines(); text='\n'.join(raw[src['start']-1:src['end']])
        if s['kind']=='declaration':
            matches=[r for r in contracts if r['symbol']==s['symbol'] and r['declaration']==src and r['configuration']==s['condition']]
            if len(matches)==1:
                r=matches[0];text=r['text'];records.append({'snippet_index':i,**{k:v for k,v in r.items() if k!='text'}})
            else:gaps.append({'symbol':s['symbol'],'declaration':src,'configuration':s['condition'],'reason':'processed callee interface missing or ambiguous'})
        lines.append('/* Original condition: '+s['condition'].replace('*/','* /').replace('\n',' ')+' */\n')
        lines.append(block('snippet-'+str(i),text))
    raw=inside(root,node['source']['path']).read_text().splitlines()
    lines.append(block('implementation','\n'.join(raw[node['source']['start']-1:node['source']['end']])))
    return '\n'.join(lines),records,gaps


def run_extract(root,output,manifest,materials,factory,*,contracts=(),budgets=None,concurrency=2,label='fixture',model_identity=None):
    root=Path(root).resolve(strict=True);output=Path(output).resolve()
    if output.is_relative_to(root):raise ValueError('preparation output must be outside input')
    if concurrency<1:raise ValueError('concurrency must be positive')
    inventory=snapshot(root)
    if manifest.get('expected_input_snapshot',inventory)!=inventory:raise ValueError('input differs from module plan')
    if manifest.get('selection_inventory',{}).get('scope_status')!='enumerated':raise ValueError('complete selected group required')
    output.mkdir(parents=True,exist_ok=False)
    state={'version':1,'status':'extracting','input_root':str(root),'original_manifest':manifest,'input_snapshot':inventory,'model':model_identity,
           'functions':{},'proof_status':'not_proved'}
    write_json(output/'preparation.json',state)
    selected={n['id']:n for n in manifest['functions']}
    def worker(node):
        ident=node['id'];folder=output/'tasks'/ident
        instructions=extraction_prompt(node,list(selected.values())[:16])+"\nINDEPENDENT PREPARATION: Extract target implementation, callee declarations, macros and type prerequisites ONLY. Do not extract reference implementations, callee bodies, or infer/write callee specifications. Callee contracts are imported by the program from previously processed interfaces. Missing source dependencies remain explicit. Return no reference snippets."
        def validator(r,reader,reads):
            errors=validate_extraction(r,reader,reads,node=node,selected=selected)
            if isinstance(r,dict) and any(s.get('kind')=='reference' for s in r.get('snippets',[]) if isinstance(s,dict)):errors.append('reference/callee implementation extraction is disabled')
            return errors
        artifacts=material_pages(node,materials)
        cards=list(selected.values())
        for start in range(0,len(cards),16):artifacts['selected-identities:'+str(start//16+1)]=cards[start:start+16]
        result=run_task(root,folder,factory('extract_source',ident),instructions,validator,role='extract_source',task_id=ident,
            budgets=budgets or Budgets(),artifacts=artifacts,label=label,allow_report_patch=True)
        entry={'node':node,'task':{k:result.get(k) for k in ('status','reason','calls')}}
        if result['status']=='task_completed':
            report=copy.deepcopy(result['report']);text,bindings,gaps=assemble(root,node,report,contracts)
            for i,s in enumerate(report['snippets']):s['part']='snippet-'+str(i)
            name=ident+'.c';write_text(output/name,text)
            entry.update(file=name,initial_sha256=sha(output/name),report=report,callee_interfaces=bindings,interface_gaps=gaps,
                         review={'approved':False,'configuration':'','changes':''})
        return ident,entry
    with ThreadPoolExecutor(max_workers=concurrency) as pool:
        futures={pool.submit(worker,n):n['id'] for n in selected.values()}
        for f in as_completed(futures):
            ident=futures[f]
            try:_,entry=f.result()
            except Exception as exc:entry={'node':selected[ident],'task':{'status':'failed','reason':str(exc)}}
            state['functions'][ident]=entry;write_json(output/'preparation.json',state)
    state['status']='awaiting_source_review' if all('file' in e for e in state['functions'].values()) else 'extraction_incomplete'
    if snapshot(root)!=inventory:state['status']='input_changed'
    write_json(output/'preparation.json',state)
    write_text(output/'REVIEW.md','# 源码准备，尚未审核\n\n每个函数只有一个 .c 文件。请修改代码、声明及QCP规约、宏、类型；保留 preparation 区段标记。\n在 preparation.json 同步维护 report 的 snippets/calls/macro_expansions（删分支后删除对应项并更新索引）、coverage、unknowns 与 callee_interfaces。\ncallee 接口按原始声明坐标和配置匹配，不按名称猜测；缺失接口先补齐。审核各函数后填写 review.approved=true、configuration、changes。\napprove 命令只固化已经填写的审核记录，不代替人工审核、编译或证明。\n')
    return state


def compile_entry(root,entry):
    path=inside(root,entry['file']);text=path.read_text();lines,parts=parse_parts(text)
    ident=entry['node']['id'];virtual='prepared/'+ident+'/'+ident+'.c'
    review=entry.get('review',{})
    if review.get('approved') is not True or not all(isinstance(review.get(k),str) and review[k].strip() for k in ('configuration','changes')):
        raise ValueError('explicit per-function review, configuration and change note required: '+ident)
    definitions,syntax_gaps=scan_c(text,virtual)
    if syntax_gaps or len(definitions)!=1 or definitions[0]['symbol']!=entry['node']['symbol']:
        raise ValueError('reviewed C must contain exactly the target implementation; resolve conditional definitions and callee bodies')
    report=copy.deepcopy(entry['report']);node=copy.deepcopy(entry['node'])
    def source(part):
        if part not in parts:raise ValueError('missing source section '+part)
        a,b=parts[part];return {'path':virtual,'start':a,'end':b}
    node['source']=source('implementation');node['configuration']=review['configuration']
    actual=definitions[0]['source']
    if not node['source']['start']<=actual['start']<=actual['end']<=node['source']['end']:
        raise ValueError('target implementation must stay inside implementation section')
    for i,s in enumerate(report['snippets']):s['source']=source(s.get('part','snippet-'+str(i)))
    def site(call,span):
        a,b=span['start'],span['end'];code=mask_noncode('\n'.join(lines[a-1:b]));pattern=r'\b'+re.escape(call['symbol'])+r'\b'
        # Full owner interval is evidence; caller/parent linkage is validated below.
        if not re.search(pattern,code):raise ValueError('recorded call absent after editing: '+call['symbol'])
        return dict(span)
    for c in report['calls']:c['callsite']=site(c,node['source'])
    units=[]
    for i,s in enumerate(report['snippets']):
        if s['kind']=='macro':
            for unit in locate(lines,s['source'],s['symbol']):unit['snippet_index']=i;units.append(unit)
    for c in report.get('macro_expansions',[]):
        matches=[u for u in units if u['snippet_index']==c['macro_index'] and re.search(r'\b'+re.escape(c['symbol'])+r'\b',mask_noncode('\n'.join(lines[u['source']['start']-1:u['source']['end']]))) ]
        if len(matches)!=1:raise ValueError('macro call must identify one reviewed definition')
        c['callsite']=dict(matches[0]['source'])
    if any(x!='checked' for x in report['coverage'].values()) or any(u.get('blocking') for u in report['unknowns']):
        raise ValueError('source dependencies must be resolved before approval')
    bindings=entry.get('callee_interfaces',[]);matched=set();contract_sources=[]
    for c in report['calls']+report.get('macro_expansions',[]):
        idx=c.get('declaration_index')
        if c.get('unresolved') or type(idx) is not int or not 0<=idx<len(report['snippets']):raise ValueError('unresolved callee or macro before approval')
        s=report['snippets'][idx]
        if s['kind']!='declaration':continue
        matches=[r for r in bindings if r.get('snippet_index')==idx and r.get('symbol')==c['symbol']]
        if len(matches)!=1 or matches[0].get('status') not in ('reviewed','proved') or matches[0].get('format')!='qcp':raise ValueError('processed callee specification required: '+c['symbol'])
        if idx not in matched:
            matched.add(idx);r=matches[0];src=s['source'];segment='\n'.join(lines[src['start']-1:src['end']])
            if segment.strip()==mask_noncode(segment).strip():raise ValueError('callee specification annotations missing')
            contract_sources.append({'symbol':c['symbol'],'source':src,'status':'human_reviewed_interface_not_reproved','upstream':r})
    # Detect obvious new function-like calls omitted by a manual edit. Human review still covers indirect calls.
    body=mask_noncode('\n'.join(lines[node['source']['start']-1:node['source']['end']]))
    names=set(re.findall(r'\b([A-Za-z_]\w*)\s*\(',body))-{'if','for','while','switch','sizeof','_Alignof',node['symbol']}
    if names-{c['symbol'] for c in report['calls']}:raise ValueError('unrecorded calls after editing: '+str(sorted(names-{c['symbol'] for c in report['calls']})))
    report['callee_contracts']=contract_sources
    return node,report,units,text,virtual


def approve(source,output,*,reviewer,note):
    source=Path(source).resolve(strict=True);output=Path(output).resolve()
    if not reviewer.strip() or not note.strip():raise ValueError('reviewer and note required')
    if output.exists() or output.is_relative_to(source):raise ValueError('approval destination must be new and outside editable preparation')
    data=json.loads((source/'preparation.json').read_text());expected=data['original_manifest']['functions']
    if output.is_relative_to(Path(data['input_root']).resolve()):raise ValueError('approval output must remain outside original input')
    if snapshot(data['input_root'])!=data['input_snapshot']:raise ValueError('original input changed during source preparation')
    if set(data['functions'])!={n['id'] for n in expected}:raise ValueError('preparation does not cover selected group')
    compiled={}
    for n in expected:
        e=data['functions'][n['id']]
        if e.get('node')!=n:raise ValueError('original function identity changed')
        compiled[n['id']]=compile_entry(source,e)
    nodes={i:v[0] for i,v in compiled.items()}
    with tempfile.TemporaryDirectory() as tmp:
        temporary=Path(tmp)
        for i,(node,report,units,text,virtual) in compiled.items():
            target=temporary/virtual;target.parent.mkdir(parents=True,exist_ok=True);target.write_text(text)
        for i,(node,report,units,text,virtual) in compiled.items():
            reader=Reader(temporary,temporary/(i+'.reads'))
            count=len(text.splitlines())
            for start in range(1,count+1,80):reader.execute({'tool':'read','path':virtual,'start':start,'count':min(80,count-start+1)})
            errors=validate_extraction(report,reader,set(),node=node,selected=nodes)
            if errors:raise ValueError('reviewed source metadata invalid: '+str(errors))
    output.mkdir(parents=True)
    result={'version':1,'status':'source_reviewed','reviewer':reviewer,'review_note':note,'original_manifest':data['original_manifest'],
            'input_snapshot':data['input_snapshot'],'functions':{},'proof_status':'not_proved'}
    for i,(node,report,units,text,virtual) in compiled.items():
        name=i+'.c';write_text(output/name,text);h=sha(output/name);span={'path':name,'start':1,'end':len(text.splitlines())}
        manifest={'version':2,'function_id':i,'configuration':node['configuration'],'source_kind':'reviewed_preparation',
                  'files':{name:h},'mappings':[{'bundle':span,'original':{**span,'path':virtual},'sha256':h}],
                  'report':report,'macro_units':units,'implementation':{**node['source'],'path':name},
                  'provenance':{'original_node':data['functions'][i]['node'],'reviewed_preparation_metadata':data['functions'][i]['report'],
                                'initial_sha256':data['functions'][i]['initial_sha256'],'review':data['functions'][i]['review']},
                  'status':'human_reviewed_not_compiled_not_proved'}
        result['functions'][i]={'node':node,'bundle':manifest,'file':name}
    write_json(output/'prepared.json',result)
    return result


def load_approved(source,manifest,inventory):
    source=Path(source).resolve(strict=True);data=json.loads((source/'prepared.json').read_text())
    if data.get('status')!='source_reviewed' or data.get('original_manifest')!=manifest or data.get('input_snapshot')!=inventory:
        raise ValueError('approved preparation does not match module plan/input')
    if set(data['functions'])!={n['id'] for n in manifest['functions']}:raise ValueError('approved scope mismatch')
    for i,e in data['functions'].items():
        verify_bundle(source,e['bundle'])
        if e['node']['id']!=i or e['bundle'].get('source_kind')!='reviewed_preparation':raise ValueError('invalid approved function identity')
    return data


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='command',required=True)
    ex=sub.add_parser('extract');ex.add_argument('--input',default='input');ex.add_argument('--manifest',required=True);ex.add_argument('--output',required=True)
    ex.add_argument('--callee-contracts',required=True);ex.add_argument('--model',default='gpt-6.1-sol');ex.add_argument('--reasoning-effort',default='high')
    ex.add_argument('--context-chars',type=int,default=80000);ex.add_argument('--calls',type=int,default=24);ex.add_argument('--concurrency',type=int,default=2)
    ap=sub.add_parser('approve');ap.add_argument('--source',required=True);ap.add_argument('--output',required=True);ap.add_argument('--reviewer',required=True);ap.add_argument('--note',required=True)
    args=parser.parse_args()
    try:
        if args.command=='approve':result=approve(args.source,args.output,reviewer=args.reviewer,note=args.note)
        else:
            from stage1.model_factory import ModelConfig, create_model
            manifest,materials=load_manifest(args.manifest,args.input);model=create_model(ModelConfig(model=args.model,reasoning_effort=args.reasoning_effort))
            result=run_extract(args.input,args.output,manifest,materials,model_factory(ModelConfig(model=args.model,reasoning_effort=args.reasoning_effort)),
                contracts=load_contracts(args.callee_contracts),budgets=Budgets(calls=args.calls,context_chars=args.context_chars),concurrency=args.concurrency,label='real_codex',model_identity=model.metadata())
        print(json.dumps({'status':result['status'],'functions':len(result['functions'])},ensure_ascii=False));return 0 if result['status'] in ('source_reviewed','awaiting_source_review') else 1
    except (ValueError,OSError) as exc:parser.error(str(exc))


if __name__=='__main__':raise SystemExit(main())

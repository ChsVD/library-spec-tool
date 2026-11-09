"""Bounded function sessions, caller-first batches and persistent graph checkpoints."""
import copy
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import partial
import hashlib
import json
from pathlib import Path
from stage1.reader import Reader
from stage1.runner import snapshot
from stage1.task import Budgets, run_task, write_json, write_text
from . import contracts
from .graph import validate_manifest, new_graph, merge_discovery, layers, context, install_spec, digest
from .prompts import prompt
from .inventory import validate_selection_manifest, expand_selection, progress

TITLES = dict(zip(contracts.SECTIONS, ('抽象含义','环境条件','输入与前置条件','结果保证','状态与资源','边界与分支')))


def render(spec):
    lines = ['# '+spec['function_id']+'：自然语言候选规约', '', '尚未证明；检查状态见 graph.json 和对应独立审查。', '']
    for k,t in TITLES.items(): lines += ['## '+t, '', spec['sections'][k], '']
    for k,t in [('claims','条款来源'),('call_requirements','对下层的调用需求（不是保证）'),
                ('caller_scenarios','调用者使用场景（推断而非保证）'),('reference_uses','参考适配'),('common_needs','公共内容需求'),('conditional_assumptions','尚未证实的依赖假设（不代表缺口已解决）'),('unknowns','未知项')]:
        lines += ['## '+t, '', '```json', json.dumps(spec.get(k,[]),ensure_ascii=False,indent=2), '```', '']
    return '\n'.join(lines)


def render_graph(graph):
    lines=['# 函数规约与调用关系', '', '箭头从调用者指向被调用者。边上是使用需求，不是已证明保证。',
           '只覆盖所选范围；未知调用和未读调用者仍须保留。规约内容及状态见 graph.json。', '', '```mermaid','graph TD']
    ids={key:'n'+str(i) for i,key in enumerate(graph['nodes'])}
    for key,n in graph['nodes'].items():
        lines.append('  '+ids[key]+'["'+key+' / '+n['status']+'"]')
    for i,e in enumerate(graph['edges'].values()):
        target=ids.get(e['callee'])
        if target is None:
            target='unknown'+str(i);lines.append('  '+target+'["unresolved target"]')
        arrow='-->' if e['certainty']=='direct' else '-.->'
        lines.append('  '+ids[e['caller']]+' '+arrow+' '+target)
    lines+=['```','','## 已选择的函数','']
    for key,n in graph['nodes'].items():
        if n['selected']:
            lines.append('- '+key+'：'+n['status']+'；规约版本 '+str(n['revision']))
    return '\n'.join(lines)+'\n'


def load_manifest(path, root=None):
    path = Path(path).resolve(strict=True)
    value = json.loads(path.read_text(encoding='utf-8-sig'))
    if value.get('version')==2: validate_selection_manifest(value)
    else: validate_manifest(value)
    materials = {}
    for key, record in value.get('materials',{}).items():
        if not isinstance(record,dict) or not isinstance(record.get('path'),str):
            raise ValueError('material path and sha256 required')
        target = (path.parent / record['path']).resolve(strict=True)
        data = target.read_bytes()
        if hashlib.sha256(data).hexdigest() != record.get('sha256'):
            raise ValueError('material changed: '+key)
        materials[key] = data.decode('utf-8-sig')
    if 'input_snapshot' in value:
        record=value['input_snapshot']
        data=(path.parent/record['path']).resolve(strict=True).read_bytes()
        if hashlib.sha256(data).hexdigest()!=record['sha256']:
            raise ValueError('stage 1 input snapshot changed')
        value['expected_input_snapshot']=json.loads(data)
    if value.get('version')==2:
        if root is None: raise ValueError('module/group manifest requires input root for enumeration')
        value=expand_selection(root,value)
    return value, materials


def material_pages(node, materials, page_chars=6000):
    pages = {}
    for key in node['materials']:
        text = materials[key]
        for offset in range(0,len(text),page_chars):
            pages[f'material:{key}:{offset//page_chars+1}'] = {
                'kind':'derived_material_not_original_evidence','material':key,
                'page':offset//page_chars+1,'total_pages':(len(text)+page_chars-1)//page_chars,
                'text':text[offset:offset+page_chars]}
    return pages


def run_pipeline(root, output, manifest, materials, model_factory, *, budgets=None,
                 batch_size=2, concurrency=2, max_revisions=1, resume=False,
                 label='fixture', model_identity=None, local_chars=18000):
    """Each function has a separate conversation, even in a scheduling batch."""
    import fcntl
    if manifest.get('version')==2: manifest=expand_selection(root,manifest)
    if not (manifest.get('selection_inventory',{}).get('gaps') and not manifest.get('functions')):
        validate_manifest(manifest)
    if min(batch_size, concurrency, local_chars)<1 or max_revisions<0: raise ValueError('invalid limits')
    budgets = budgets or Budgets(context_chars=60000)
    root, output = Path(root).resolve(strict=True), Path(output).resolve()
    if output.is_relative_to(root): raise ValueError('output must be outside input')
    if resume:
        if not output.is_dir(): raise ValueError('resume output missing')
    else: output.mkdir(parents=True,exist_ok=False)
    with (output/'run.lock').open('a') as lock:
        try: fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError: raise ValueError('run already active')
        return _run(root,output,manifest,materials,model_factory,budgets,batch_size,concurrency,
                    max_revisions,resume,label,model_identity,local_chars)


def _run(root,output,manifest,materials,factory,budgets,batch_size,concurrency,max_revisions,resume,label,model_identity,local_chars):
    inventory = snapshot(root)
    if 'expected_input_snapshot' in manifest and manifest['expected_input_snapshot'] != inventory:
        raise ValueError('input differs from stage 1 materials; recheck affected analysis')
    identity = {'manifest':manifest, 'materials':{k:digest(v) for k,v in materials.items()},
                'model':model_identity or {'mode':label}, 'mode':label}
    reader = Reader(root,output/'preflight-reads.jsonl')
    for node in manifest['functions']:
        source=node['source']; lines,_=reader.lines(source['path'])
        if source['end']>len(lines): raise ValueError('function source interval exceeds file')
    if resume:
        if json.loads((output/'identity.json').read_text())!=identity:
            raise ValueError('resume manifest/material/model differs')
        if json.loads((output/'input_snapshot.json').read_text())!=inventory:
            raise ValueError('resume input changed')
        graph=json.loads((output/'graph.json').read_text())
        state=json.loads((output/'status.json').read_text())
        if digest(graph)!=state.get('graph_digest'):
            raise ValueError('checkpoint graph/status mismatch; inspect saved tasks before recovery')
    else:
        graph=new_graph(manifest)
        state={'stage':2,'mode':label,'status':'running','tasks':{},'attempt':0,'proof_status':'not_proved',
               'scope_decision':manifest['scope_decision']}
        write_json(output/'identity.json',identity); write_json(output/'input_snapshot.json',inventory)
    state['status']='running'
    def persist():
        write_json(output/'graph.json',graph)
        write_text(output/'graph.md',render_graph(graph))
        state['selection_progress']=progress(graph)
        write_json(output/'selection_progress.json',state['selection_progress'])
        if 'selection_inventory' in graph: write_json(output/'selection_inventory.json',graph['selection_inventory'])
        state['graph_digest']=digest(graph)
        write_json(output/'status.json',state)
    def changed():
        if snapshot(root)!=inventory:
            state.update(status='input_changed',reason='input changed; saved candidates are not publishable')
            persist(); return True
        return False
    def run(role, ident, validator, assignment, artifacts):
        # Called with a unique counter allocated by the main thread.
        return run_task(root,output/'tasks'/ident,factory(role,ident),prompt(role,assignment),validator,
                        role=role,task_id=ident,budgets=budgets,artifacts=artifacts,label=label,allow_report_patch=True)
    def next_id(role,ident):
        state['attempt']+=1; persist()
        return f"{role}-{ident}-{state['attempt']:04d}"
    def record(ident,result):
        state['tasks'][ident]={k:result.get(k) for k in ('status','reason','calls','elapsed_seconds')}
        persist()
    def execute(role, node, validator, assignment, artifacts):
        ident=next_id(role,node['id'])
        result=run(role,ident,validator,assignment,artifacts); record(ident,result)
        return result,ident
    def artifacts_for(node,view,previous=None,review=None):
        artifacts=material_pages(node,materials)
        for n in view['neighbors']:
            spec=graph['nodes'][n['id']]['spec']
            if spec: artifacts['neighbor:'+n['id']]=spec
        if previous: artifacts['previous_candidate']=previous
        if review: artifacts['revision_review']=review
        return artifacts
    def inspect(node,spec,view):
        artifacts=artifacts_for(node,view); artifacts['candidate']=spec
        return execute('review',node,partial(contracts.review,node=node,spec=spec,graph=graph),view,artifacts)
    # Unaccepted drafts are only derived repair input; source evidence must be read again.
    saved_drafts = {}
    if resume:
        for candidate in sorted((output/'tasks').glob('write-*/draft.json'), key=lambda p:p.stat().st_mtime):
            value=json.loads(candidate.read_text()).get('interpretation')
            if isinstance(value,dict) and value.get('function_id') in graph['nodes'] and isinstance(value.get('sections'),dict):
                if len(json.dumps(value,ensure_ascii=False))<=18000:
                    saved_drafts[value['function_id']]={'status':'unvalidated_previous_draft',
                        'source_task':str(candidate.parent.relative_to(output)), 'report':value,
                        'warning':'Not accepted. Read original evidence afresh; check every field and do not inherit proof/check status.'}
    persist()
    try:
        if graph.get('selection_inventory',{}).get('scope_status')=='needs_scope_review':
            state.update(status='needs_scope_review',reason='inventory gaps must be resolved; all enumerated functions remain pending')
            persist(); return state
        # Discover one selected function at a time. Neighbors are context-only unless selected in the manifest.
        for node in manifest['functions']:
            if node['id'] in graph['discoveries']: continue
            known={k:{f:n[f] for f in ('id','symbol','source','configuration')} for k,n in graph['nodes'].items()}
            # Only same-file known identities are supplied; the global graph is never injected.
            known_local={k:n for k,n in known.items() if n['source']['path']==node['source']['path']}
            if len(json.dumps(known_local,ensure_ascii=False))>local_chars//2:
                known_local={node['id']:known[node['id']]}  # Remaining identities stay in paged index, never deselected.
            assignment={'function':node,'known_same_file':known_local,'scope_decision':manifest['scope_decision']}
            if len(json.dumps(assignment,ensure_ascii=False))>local_chars:
                raise ValueError('discovery context too large; reduce selected scope')
            index_artifacts={}
            # Cross-file selected functions keep their canonical IDs. Index cards are
            # paged and contain identities only, never all specs or implementations.
            selected_cards=[n for k,n in known.items() if graph['nodes'][k]['selected']]
            for offset in range(0,len(selected_cards),16):
                index_artifacts['selected-functions:'+str(offset//16+1)]=selected_cards[offset:offset+16]
            assignment['identity_rule']='All functions selected by the module/group inventory stay selected. Reuse known_same_file or paged selected-functions identities; never create a second ID for the same definition. Do not replace the group with one promising function.'
            result,tid=execute('discover',node,partial(contracts.discovery,node=node,known=known),
                               assignment,{**material_pages(node,materials),**index_artifacts})
            if result['status']!='task_completed':
                state.update(status='incomplete',reason='discovery incomplete: '+tid); persist(); return state
            merge_discovery(graph,result['report']); persist()
        if changed(): return state
        schedule=layers(graph); write_json(output/'schedule.json',schedule)
        for layer in schedule:
            ids=[ident for group in layer for ident in group]
            for start in range(0,len(ids),batch_size):
                batch=ids[start:start+batch_size]
                for revision in range(max_revisions+1):
                    jobs={}
                    with ThreadPoolExecutor(max_workers=min(concurrency,batch_size)) as pool:
                        for ident in batch:
                            node=graph['nodes'][ident]
                            if node['status'] in ('reviewed_candidate','needs_recheck','insufficient','tool_blocked'): continue
                            if node['status']=='needs_revision' and revision==0 and not resume: continue
                            view=context(graph,ident,local_chars)
                            group=next(g for g in layer if ident in g)
                            view['cycle_assumptions']=len(group)>1 or any(e['caller']==ident==e['callee'] for e in graph['edges'].values())
                            tid=next_id('write',ident)
                            artifacts=artifacts_for(node,view,node['spec'],node['review'])
                            if ident in saved_drafts and node['spec'] is None:
                                artifacts['unvalidated_previous_draft']=saved_drafts[ident]
                                view['repair_instruction']='First inspect unvalidated_previous_draft; repair its gaps using focused original reads. This is not an accepted spec. Avoid rereading unrelated headers or whole files; read exact relevant intervals.'
                            frozen=copy.deepcopy(graph)
                            validator=partial(contracts.specification,node=node,graph=frozen)
                            jobs[pool.submit(run,'write',tid,validator,view,artifacts)]=(ident,tid)
                        for future in as_completed(jobs):
                            ident,tid=jobs[future]
                            try: result=future.result()
                            except Exception as exc: result={'status':'failed','reason':str(exc)}
                            record(tid,result)
                            if result['status']!='task_completed':
                                graph['nodes'][ident]['status']='incomplete'; persist(); continue
                            spec=result['report']; node=graph['nodes'][ident]
                            folder=output/'functions'/ident; folder.mkdir(parents=True,exist_ok=True)
                            version=f"candidate-{state['attempt']:04d}-{revision}"
                            write_json(folder/(version+'.json'),spec); write_text(folder/(version+'.md'),render(spec))
                            review_result,review_id=inspect(node,spec,context(graph,ident,local_chars))
                            if review_result['status']!='task_completed':
                                node.update(status='incomplete',spec=spec,review=None); persist(); continue
                            review=review_result['report']
                            write_json(folder/(version+'-review.json'),review)
                            install_spec(graph,ident,spec,review)
                            node=graph['nodes'][ident]
                            node['candidate_file']=str((folder/(version+'.json')).relative_to(output))
                            node['review_task']=review_id
                            persist()
                    if changed(): return state
                    if not any(graph['nodes'][i]['status']=='needs_revision' for i in batch): break
                # Each function is committed before moving to the next batch.
        # New lower-level candidates invalidate earlier neighbor assumptions. Recheck only,
        # do not rewrite specs here or claim a fixed point for recursive specifications.
        for ident,node in graph['nodes'].items():
            if not node['selected'] or node['status']!='needs_recheck': continue
            result,tid=inspect(node,node['spec'],context(graph,ident,local_chars))
            if result['status']=='task_completed':
                node['review']=result['report']; node['review_task']=tid
                node['status']='reviewed_candidate' if result['report']['verdict']=='pass' else result['report']['verdict']
            else: node['status']='incomplete'
            persist()
        if changed(): return state
        selected={k:n['status'] for k,n in graph['nodes'].items() if n['selected']}
        state['functions']=selected
        state['status']='candidates_reviewed' if progress(graph)['all_selected_complete'] else 'incomplete'
        state['reason']='natural-language candidates only; no formal proof or automatic phase 3'
        persist()
        lines=['# 阶段 2 运行结果','',state['status'],'','候选均未证明；图只覆盖所选范围及发现的邻接关系。','',
               '选择范围：'+str(progress(graph)['selection_id'] or '历史显式函数清单'),
               '已审查 '+str(progress(graph)['reviewed_count'])+' / '+str(progress(graph)['expected_count'])+' 个选定函数；批大小不会缩小选择范围。','']
        for ident in selected:
            n=graph['nodes'][ident]
            lines.append('- '+ident+'：'+n['status'])
            if n['spec']:
                folder=output/'functions'/ident; folder.mkdir(parents=True,exist_ok=True)
                write_text(folder/'candidate.md',render(n['spec']))
                write_json(folder/'candidate.json',n['spec'])
                lines.append('  [自然规约](functions/'+ident+'/candidate.md)')
        write_text(output/'SUMMARY.md','\n'.join(lines)+'\n')
        return state
    except KeyboardInterrupt:
        state.update(status='interrupted',reason='user interrupt'); persist(); return state
    except Exception as exc:
        state.update(status='failed',reason=str(exc)); persist(); return state

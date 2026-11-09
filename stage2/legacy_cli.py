"""Run stage 2 against an module/group manifest (legacy function lists remain supported)."""
from stage1.model_factory import ModelConfig, create_model, model_factory
import argparse
import json
from stage1.codex_backend import BackendError
from stage1.task import Budgets
from .pipeline import load_manifest, run_pipeline


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',default='input')
    p.add_argument('--manifest',required=True)
    p.add_argument('--output',required=True)
    p.add_argument('--resume',action='store_true')
    p.add_argument('--workflow',choices=['bundles','legacy'],default='bundles',help='bundles consumes reviewed prepared source; legacy preserves old runs')
    p.add_argument('--prepared-source',help='reviewed output from python -m stage2.prepare approve; required for bundles')
    p.add_argument('--qcp-examples',help='explicit NEW directory for exporting extracted source bundles; existing examples never overwritten')
    p.add_argument('--with-common',action='store_true',help='after complete group review, automatically generate and review stage3 common candidates')
    p.add_argument('--common-output',help='stage3 output; defaults to stage2 output plus -common')
    p.add_argument('--allow-legacy-function-list',action='store_true',help='explicitly opt into historical single/function-list experiments; not module/group completion')
    p.add_argument('--model',default='gpt-6.1-sol')
    p.add_argument('--reasoning-effort',default='high',choices=['low','medium','high','xhigh','max'])
    p.add_argument('--batch-size',type=int,default=2)
    p.add_argument('--concurrency',type=int,default=2)
    p.add_argument('--max-revisions',type=int,default=1)
    p.add_argument('--calls',type=int,default=24)
    p.add_argument('--seconds',type=float,default=1800)
    p.add_argument('--call-timeout',type=float,default=600)
    p.add_argument('--context-chars',type=int,default=60000)
    p.add_argument('--local-chars',type=int,default=18000)
    p.add_argument('--prepare-only',action='store_true',help='check manifest, material hashes and source snapshot without model calls')
    args=p.parse_args()
    try:
        if args.qcp_examples:
            from pathlib import Path
            target=Path(args.qcp_examples).resolve()
            if target.exists() or target.is_relative_to(Path(args.input).resolve()):raise ValueError('QCP export needs a new directory outside input')
        manifest,materials=load_manifest(args.manifest,args.input)
        if 'selection_inventory' not in manifest and not args.allow_legacy_function_list:
            raise ValueError('use a version=2 module/function_group manifest; historical function lists require --allow-legacy-function-list')
        if args.prepare_only:
            from stage1.runner import snapshot
            if manifest.get('expected_input_snapshot',snapshot(args.input))!=snapshot(args.input):
                raise ValueError('input differs from stage 1 snapshot')
            from pathlib import Path
            from stage1.task import write_json, write_text
            destination=Path(args.output).resolve()
            if destination.is_relative_to(Path(args.input).resolve()):raise ValueError('prepare output must be outside input')
            if manifest.get('selection_inventory',{}).get('selection',{}).get('kind') == 'module':
                from .frontier import plan, save
                result = plan(args.input, manifest)
                save(result, destination)
                print(json.dumps({'status':result['status'],'function_count':len(result['functions']),
                                  'output':str(destination)},ensure_ascii=False))
                return 0
            destination.mkdir(parents=True,exist_ok=False)
            inventory=manifest.get('selection_inventory',{'scope_status':'legacy_function_list'})
            prepared={'status':'needs_scope_review' if inventory.get('scope_status')=='needs_scope_review' else 'prepared_not_run',
                      'selection_inventory':inventory,'functions':manifest['functions'],
                      'material_pages':{k:(len(v)+5999)//6000 for k,v in materials.items()}}
            write_json(destination/'INVENTORY.json',prepared)
            lines=['# 待处理函数清单','','状态：'+prepared['status'], '',
                   '选择范围内共 '+str(len(manifest['functions']))+' 个函数，全部待处理；批大小不是总数上限。','']
            for n in manifest['functions']:
                lines.append('- '+n['symbol']+' — '+n['source']['path']+':'+str(n['source']['start'])+'-'+str(n['source']['end'])+'；待处理')
            if inventory.get('gaps'):lines+=['','## 未解析范围','',json.dumps(inventory['gaps'],ensure_ascii=False,indent=2)]
            write_text(destination/'FUNCTION_INDEX.md','\n'.join(lines)+'\n')
            print(json.dumps({'status':prepared['status'],'function_count':len(manifest['functions']),
                              'symbols':[n['symbol'] for n in manifest['functions']], 'output':str(destination)},ensure_ascii=False))
            return 0 if prepared['status']=='prepared_not_run' else 1
        if args.workflow=='bundles' and not args.prepared_source:
            raise ValueError('bundles now requires --prepared-source; run python -m stage2.prepare extract, review the C files, then approve separately')
        budgets=Budgets(calls=args.calls,seconds=args.seconds,context_chars=args.context_chars,
                        call_timeout_seconds=args.call_timeout)
        model=create_model(ModelConfig(model=args.model,reasoning_effort=args.reasoning_effort))
        pipeline=run_pipeline
        if args.workflow=='bundles':
            from .bundled import run_pipeline as bundled_pipeline
            pipeline=bundled_pipeline
        result=pipeline(args.input,args.output,manifest,materials,
            model_factory(ModelConfig(model=args.model,reasoning_effort=args.reasoning_effort)),
            budgets=budgets,batch_size=args.batch_size,concurrency=args.concurrency,max_revisions=args.max_revisions,
            resume=args.resume,label='real_codex',model_identity=model.metadata(),local_chars=args.local_chars,
            **({'prepared_source':args.prepared_source} if args.workflow=='bundles' else {}))
        if args.qcp_examples:
            if args.workflow!='bundles':raise ValueError('--qcp-examples requires bundled workflow')
            from .bundled import export_examples
            export_examples(args.output,args.qcp_examples)
        if args.with_common and result['status']=='candidates_reviewed':
            from pathlib import Path
            from stage4.pipeline import run_pipeline as run_common
            common_output=Path(args.common_output or str(args.output)+'-common')
            result=run_common(args.input,common_output,args.output,
                model_factory(ModelConfig(model=args.model,reasoning_effort=args.reasoning_effort)),
                budgets=budgets,max_revisions=args.max_revisions,
                resume=args.resume and common_output.is_dir(),label='real_codex',model_identity=model.metadata())
            print(json.dumps(result,ensure_ascii=False,indent=2))
            return 0 if result['status']=='common_candidates_reviewed' else 1
        print(json.dumps(result,ensure_ascii=False,indent=2))
        return 0 if result['status']=='candidates_reviewed' else 1
    except (ValueError,OSError,BackendError) as exc: p.error(str(exc))


if __name__=='__main__': raise SystemExit(main())

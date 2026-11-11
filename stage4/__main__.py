"""Find reusable references for selected functions using complete stage-three specifications."""
from stage1.model_factory import ModelConfig, create_model, model_factory
import argparse
import json
from stage1.codex_backend import BackendError
from stage1.task import Budgets
from .pipeline import run_pipeline


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',default='input');p.add_argument('--stage3-run','--stage2-run',dest='stage3_run',required=True,help='natural-specification run; --stage2-run is a legacy alias')
    p.add_argument('--output',required=True);p.add_argument('--resume',action='store_true')
    p.add_argument('--model',default='gpt-6.1-sol');p.add_argument('--reasoning-effort',default='high')
    p.add_argument('--calls',type=int,default=24);p.add_argument('--seconds',type=float,default=1800)
    p.add_argument('--call-timeout',type=float,default=600);p.add_argument('--context-chars',type=int,default=60000)
    p.add_argument('--max-revisions',type=int,default=1)
    def report_limit(value):
        if value=='unlimited':return None
        try: result=int(value)
        except ValueError:raise argparse.ArgumentTypeError('expected positive integer or unlimited')
        if result<1:raise argparse.ArgumentTypeError('expected positive integer or unlimited')
        return result
    p.add_argument('--max-report-chars',type=report_limit,default=24000)
    p.add_argument('--recover-from',help='stopped stage4 run; write repaired results to a new output directory')
    p.add_argument('--component-review',action='store_true',help='compatibility option; protocol 3 always reviews references and their uses separately')
    p.add_argument('--input-transition',help='explicit additive input manifest')
    p.add_argument('--revise-from',help='reviewed run needing correction; retain old run')
    a=p.parse_args()
    try:
        model=create_model(ModelConfig(model=a.model,reasoning_effort=a.reasoning_effort))
        result=run_pipeline(a.input,a.output,a.stage3_run,
            model_factory(ModelConfig(model=a.model,reasoning_effort=a.reasoning_effort)),
            budgets=Budgets(calls=a.calls,seconds=a.seconds,call_timeout_seconds=a.call_timeout,context_chars=a.context_chars),
            max_revisions=a.max_revisions,resume=a.resume,recover_from=a.recover_from,max_report_chars=a.max_report_chars,component_review=a.component_review,input_transition=a.input_transition,revise_from=a.revise_from,label='real_codex',model_identity=model.metadata())
        print(json.dumps(result,ensure_ascii=False,indent=2))
        return 0 if result['status']=='common_candidates_reviewed' else 1
    except (ValueError,OSError,BackendError) as exc:p.error(str(exc))

if __name__=='__main__':raise SystemExit(main())

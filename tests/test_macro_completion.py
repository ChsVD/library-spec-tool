import json
import tempfile
import unittest
from pathlib import Path
from stage2.macro_units import scan,locate
from stage2.source_bundle import materialize
from stage2.bundle_reader import reader_factory
from stage1.task import run_task,Budgets,ReportPolicy
from stage1.contracts import check_evidence


class MacroUnitsTests(unittest.TestCase):
    def test_full_body_and_nested_branch_history(self):
        lines=['#if DEBUG','#if A','#define M(x) '+chr(92),'  (x)','#elif B','#define M(x) 2','#else','#define M(x) 3','#endif','#endif']
        units=scan(lines,'h.h')
        self.assertEqual(units[0]['source'],{'path':'h.h','start':3,'end':4})
        self.assertEqual([c['text'] for c in units[2]['conditions']],['#if DEBUG','#if A','#elif B','#else'])
        with self.assertRaisesRegex(ValueError,'incomplete macro'):
            locate(lines,{'path':'h.h','start':3,'end':3},'M')

    def test_comment_define_is_not_a_macro(self):
        self.assertEqual(scan(['/*','#define FAKE 1','*/','#define REAL 2'],'h.h')[0]['symbol'],'REAL')
        with self.assertRaises(ValueError):scan(['#else','#define M 1'],'h.h')
        with self.assertRaises(ValueError):scan(['#define M '+chr(92)],'h.h')

    def test_materialize_copies_outer_conditions_with_mappings(self):
        with tempfile.TemporaryDirectory() as temp:
            base=Path(temp);root=base/'input';root.mkdir()
            (root/'h.h').write_text('#if DEBUG\n#define M 1\n#else\n#define M 2\n#endif\n')
            node={'id':'f','source':{'path':'h.h','start':2,'end':2}}
            report={'snippets':[{'kind':'macro','symbol':'M','source':{'path':'h.h','start':4,'end':4}}]}
            m=materialize(root,base/'bundle',node,report)
            self.assertEqual([c['source']['start'] for c in m['macro_units'][0]['conditions']],[1,3])
            copied={x['original']['start'] for x in m['mappings']}
            self.assertTrue({1,3,4}<=copied)


class CompletionTests(unittest.TestCase):
    def run_case(self,*,copied_end=2,line='int y;',context=20000):
        tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup);base=Path(tmp.name)
        root=base/'input';root.mkdir();(root/'a.c').write_text('int x;\n'+line+'\n')
        node={'id':'f','source':{'path':'a.c','start':1,'end':copied_end}}
        m=materialize(root,base/'bundle',node,{'snippets':[]})
        readers=[];factory=reader_factory([(base/'bundle',m)])
        def capture(root,log):
            r=factory(root,log);readers.append(r);return r
        calls=[];evidence={'path':'a.c','start':2,'end':2}
        def model(messages,*_):
            calls.append(1)
            if len(calls)==2:self.assertTrue(any('Additional original source supplied' in x['content'] for x in messages))
            return json.dumps({'tool':'finish','report':{'evidence':[evidence]}})
        state=run_task(root,base/'task',model,'test',lambda r,reader,_:check_evidence(r['evidence'],reader),
            role='write',task_id='t',budgets=Budgets(calls=4,seconds=30,context_chars=context,reserve_seconds=0,reserve_chars=0),
            required_inputs=[{'tool':'read','path':'a.c','start':1,'count':1}],report_policy=ReportPolicy(1000,1000,1000,1000),
            reader_factory=capture,complete_bundle_evidence=True,allow_report_patch=True)
        return state,readers[0],base,evidence

    def test_available_evidence_delivered_then_model_rechecks(self):
        s,r,p,e=self.run_case()
        self.assertEqual(s['status'],'task_completed',s);self.assertEqual(s['calls'],2)
        self.assertTrue(json.loads((p/'task/evidence_completion.json').read_text())['delivered'])

    def test_missing_bundle_lines_never_read_original(self):
        s,r,p,e=self.run_case(copied_end=1)
        self.assertEqual(s['status'],'needs_material');self.assertEqual(s['calls'],1)
        self.assertTrue(check_evidence([e],r))
        self.assertTrue(json.loads((p/'task/evidence_completion.json').read_text())['unavailable'])

    def test_oversized_completion_rolls_back_evidence_credit(self):
        s,r,p,e=self.run_case(line='x'*6100)
        self.assertEqual(s['status'],'needs_material');self.assertEqual(s['calls'],1)
        self.assertTrue(check_evidence([e],r))
        self.assertFalse(json.loads((p/'task/evidence_completion.json').read_text())['delivered'])

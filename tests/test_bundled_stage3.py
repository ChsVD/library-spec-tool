import json
import unittest
from pathlib import Path
from tests import test_bundled_pipeline as fixtures
from tests.test_stage3 import Model
from stage4.pipeline import run_pipeline,load_upstream
from stage1.task import Budgets

class ScopedModel(Model):
    def __call__(self,messages,timeout):
        value=json.loads(super().__call__(messages,timeout))
        system=messages[0]['content'];assignment=json.JSONDecoder().raw_decode(system.split('任务：\n')[1])[0]
        if value.get('tool')=='read' and self.role=='extract':
            src=assignment['function']['source'];value.update(path=src['path'],start=src['start'],count=src['end']-src['start']+1)
        if value.get('tool')=='finish':
            packs=[];read=[]
            for message in messages[1:]:
                if message['role']!='user':continue
                try:feedback=json.loads(message['content'])
                except ValueError:continue
                if feedback.get('id')=='source-index':packs=feedback['content']
                if feedback.get('lines'):read.append(feedback)
            for pack in packs:
                for src in pack['ranges']:
                    if not all(any(r['path']==src['path'] and r['start']<=i<=r['end'] for r in read) for i in range(src['start'],src['end']+1)):
                        return json.dumps({'tool':'read','path':src['path'],'start':src['start'],'count':src['end']-src['start']+1,'draft':'independently read copied source interval'})
        if value.get('tool')=='finish' and self.role=='extract':
            value['report']['needs'][0]['evidence']=[assignment['function']['source']]
        return json.dumps(value)

class BundledStage3Tests(unittest.TestCase):
    def setUp(self):
        self.fixture=fixtures.BundledPipelineTests();self.fixture.setUp();self.addCleanup(self.fixture.doCleanups)
        result,graph,_=self.fixture.run_fixture()
        self.assertEqual(result['status'],'candidates_reviewed')
    def test_common_stage_reads_only_source_bundles(self):
        f=self.fixture;target=f.base/'common'
        result=run_pipeline(f.root,target,f.output,lambda r,t:ScopedModel(r),protocol_version=2,budgets=Budgets(calls=24,seconds=30,context_chars=60000,reserve_seconds=0))
        self.assertEqual(result['status'],'common_candidates_reviewed',result)
        for log in (target/'tasks').glob('*/reads.jsonl'):
            for line in log.read_text().splitlines():
                record=json.loads(line)
                if 'lines' in record['result']:self.assertEqual(record['result']['source'],'verified_extracted_copy')
    def test_stage3_rejects_source_bundle_tampering(self):
        f=self.fixture;g=json.loads((f.output/'graph.json').read_text())
        n=next(n for n in g['nodes'].values() if n['selected'])
        (f.output/n['source_bundle']['path']/'implementation.c').write_text('changed')
        with self.assertRaises(ValueError):load_upstream(f.root,f.output)
    def test_stage3_rejects_manifest_tampering(self):
        f=self.fixture;g=json.loads((f.output/'graph.json').read_text())
        n=next(n for n in g['nodes'].values() if n['selected'])
        p=f.output/n['source_bundle']['path']/'manifest.json';m=json.loads(p.read_text());m['configuration']='changed';p.write_text(json.dumps(m))
        with self.assertRaises(ValueError):load_upstream(f.root,f.output)

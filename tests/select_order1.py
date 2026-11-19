from pathlib import Path
import json,math,statistics
root=Path(__file__).resolve().parents[1];out=root/'evidence/order1_20261112_161356';r=json.loads((out/'screen_normal/results.json').read_text());orders=json.loads((root/'evidence/order1_inputs/cases.json').read_text())['orders']
assert len(r)==544 and not any(x['status'] in ['ERROR','MISMATCH'] for x in r)
by={(x['base_id'],x['order']):x for x in r};names=sorted({x['base_id'] for x in r if x['split']=='train'});assert len(names)==24
cost=lambda x:x['kernel_seconds'] if x['status']=='PASS' else 800.0
scores={order:math.exp(statistics.mean(math.log(cost(by[name,order])/cost(by[name,'identity'])) for name in names)) for order in orders}
selected=min(orders[:-1],key=lambda order:scores[order]);doc={'selected_order':selected,'criterion':'geometric mean of PAR2 cost ratio to identity on 24 train cases only; timeout cost=800 seconds; random_control excluded; stable tie order','train_scores':scores,'train_ids':names,'selection_did_not_use_holdout':True}
(out/'selection.json').write_text(json.dumps(doc,indent=2));print(json.dumps(doc,indent=2))

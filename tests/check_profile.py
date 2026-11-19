from pathlib import Path
import subprocess,json
root=Path(__file__).resolve().parents[1]
for config in ['one1-skip1-nb0-simple0-san0-profile1','one1-skip1-nb1-simple1-san0-profile1']:
 data=b'1 1\n1 -1\n1 1\n-1 1\n1 0\n1\n'
 # One-sided elimination would remove the first row: use a bounded pair instead.
 data=b'2 1\n1 -1\n-2 1\n2 1\n-1 -1\n-1 1\n1 0\n1\n'
 p=subprocess.run([str(root/'build'/config/'bench_driver')],input=data,capture_output=True,check=True)
 assert p.stdout.split()==[b'0',b'0',b'1']
 ss=[json.loads(x[11:]) for x in p.stderr.decode().splitlines() if x.startswith('sx_profile=')];final=[x for x in ss if x['stage']=='final'];assert len(final)==3
 assert final[0]['begun']==final[0]['completed']==1
 assert final[1]['begun']==final[1]['completed']==0 and final[1]['calls']==[0]*4
 assert final[2]['begun']==final[2]['completed']==0 and final[2]['rows']==0
 assert final[0]['peak_table_bits']>=final[0]['initial_bits'] and final[0]['arithmetic_bits']>0
 assert all(0<=x['density']<=1 and x['peak_density']>=x['density'] for x in ss)
 print(config,'reset, pivot count, density and bit-width checks passed')

import json,csv,statistics
from pathlib import Path
root=Path(__file__).resolve().parents[1];out=root/'evidence/remainder1_20261112_170832';records=json.loads((out/'results.json').read_text());assert len(records)==280
pairs={}
for x in records:pairs.setdefault(x['id'],{})[x['variant']]=x
rows=[]
for i,p in pairs.items():
 b,c=p['baseline'],p['remainder'];common=b['status']==c['status']=='PASS'
 rows.append(dict(id=i,suite=b['suite'],baseline_status=b['status'],remainder_status=c['status'],baseline_seconds=b['kernel_seconds'],remainder_seconds=c['kernel_seconds'],time_ratio=c['kernel_seconds']/b['kernel_seconds'] if common else None))
with (out/'comparison.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
lines=['# 余数优先 GCD 整体消融实验','', '日期：2026-11-12。基线开启 ONE_SIDED / SKIP_BASIC_ZERO / NONBASIC_ITER / SIMPLE_ARITH 四项；候选再开启 GCD_REMAINDER。普通构建、140 输入×2，外部每次400秒，4路固定CPU并发。输入及二进制哈希见 config.json/source_hashes.json；所有输入预期结果先经精确证书独立复核。超时不算正确判定。','', '|输入集|基线通过/超时|候选通过/超时|共同完成例累计秒：基线→候选|耗时变化|','|---|---:|---:|---:|---:|']
for suite in ['original52','stress20','seed48','qcp20']:
 rr=[x for x in rows if x['suite']==suite];valid=[x for x in rr if x['time_ratio'] is not None];b=sum(x['baseline_seconds'] for x in valid);c=sum(x['remainder_seconds'] for x in valid)
 counts=lambda v:'/'.join(str(sum(x[v+'_status']==s for x in rr)) for s in ['PASS','TIMEOUT'])
 lines.append(f'|{suite}|{counts("baseline")}|{counts("remainder")}|{b:.3f} → {c:.3f}|{(c/b-1)*100:+.1f}%|')
valid=[x for x in rows if x['time_ratio'] is not None];b=sum(x['baseline_seconds'] for x in valid);c=sum(x['remainder_seconds'] for x in valid)
lines+=['',f'共同完成 {len(valid)} 例，累计内核耗时 {b:.3f} → {c:.3f} 秒（{(c/b-1)*100:+.1f}%）。累计值受最长案例支配，不能视为每类输入的平均收益。真实 QCP 20例很小，其微秒级比例不宜解释成稳定性能结论。',f'MISMATCH/ERROR 合计：{sum(x["status"] in ["MISMATCH","ERROR"] for x in records)}。','', '## 较慢案例','', '|案例|基线秒|候选秒|耗时变化|','|---|---:|---:|---:|']
for x in sorted(valid,key=lambda x:x['baseline_seconds'],reverse=True)[:12]:lines.append(f'|{x["id"]}|{x["baseline_seconds"]:.3f}|{x["remainder_seconds"]:.3f}|{(x["time_ratio"]-1)*100:+.1f}%|')
lines+=['','## 回退案例检查','']
reg=[x for x in valid if x['baseline_seconds']>=.01 and x['time_ratio']>1]
lines+= [f'- {x["id"]}: {x["baseline_seconds"]:.6f} → {x["remainder_seconds"]:.6f} 秒（{(x["time_ratio"]-1)*100:+.1f}%）' for x in sorted(reg,key=lambda x:x['time_ratio'],reverse=True)[:8]] or ['没有基线超过10毫秒且候选变慢的案例。']
serial=out/'serial/results.json'
if serial.exists():
 sr=json.loads(serial.read_text());assert len(sr)==30 and all(x['status']=='PASS' for x in sr)
 lines+=['','## 同一CPU串行三次复测','', '独立使用已归档普通二进制，轮换顺序，下表为内核耗时中位数。','', '|案例|基线秒|候选秒|耗时变化|','|---|---:|---:|---:|']
 for i in dict.fromkeys(x['id'] for x in sr):
  med=lambda v:statistics.median(x['kernel_seconds'] for x in sr if x['id']==i and x['variant']==v)
  b,c=med('baseline'),med('remainder');lines.append(f'|{i}|{b:.6f}|{c:.6f}|{(c/b-1)*100:+.1f}%|')
profile=sorted(root.glob('evidence/remainder1_profile_*/results.json'))
if profile:
 pr=json.loads(profile[-1].read_text());assert len(pr)==10 and all(x['status']=='PASS' for x in pr)
 lines+=['','## 测试专用统计','',f'数据：{profile[-1].parent.name}。统计开销不计入正式性能结论；规范化总成本包含 GCD＋显式求余＋精确除法。','', '|案例|规范化总成本：基线→候选（秒）|显式求余秒|零余数占比|','|---|---:|---:|---:|']
 for i in dict.fromkeys(x['id'] for x in pr):
  p={x['variant']:x['profile'] for x in pr if x['id']==i};b,c=p['baseline'],p['remainder']
  assert b['phase_calls'][0][0]==c['remainder_calls']
  assert c['phase_calls'][0][0]==c['remainder_calls']-c['remainder_zero']
  assert b['gcd_kept'][0]==c['remainder_zero'] and c['gcd_kept'][0]==0
  assert b['phase_calls'][1]==c['phase_calls'][1] and b['phase_calls'][0][1]==c['phase_calls'][0][1]
  for k in ['normalizations','reductions','answer','begun','completed','rows','cols','initial_bits','table_bits','peak_table_bits','initial_density','density','peak_density']:assert b[k]==c[k]
  tb=sum(b['phase_seconds'][0]);tc=sum(c['phase_seconds'][0])+c['remainder_seconds']
  lines.append(f'|{i}|{tb:.4f} → {tc:.4f}|{c["remainder_seconds"]:.4f}|{c["remainder_zero"]/c["remainder_calls"]:.1%}|')
 lines+=['','上述次数恒等式均自动验证通过；完整表轨迹对照另有6例逐字节一致记录。']
lines+=['','## 正确性、范围及恢复','', '- 普通/ASan/UBSan：597数学案例、90次换基检查及6个规范化固定期望案例通过；分别覆盖新选项独立启用和四项叠加。6例逐次完整表轨迹字节一致。','- 关闭新选项后，生产预处理token及普通二进制.text与上一阶段相同。回退脚本在临时副本验证恢复4个原文件和写入前拒绝后续修改。','- 新选项默认关闭；仅替换规范化GCD求法，不排序、不改变换基选择、约简频率或公开0/1接口。','- 后续形式化需补充 mpz_tdiv_r 的非别名契约。现有注释只覆盖 r==n；当前独立临时量受C实现支持，但不能直接继承该证明。vendor 未改动；测试不等于形式化证明。','- 未提交或推送，历史实验保留。完整设计、开关和契约见 ../../REMAINDER1.md；回退：python3 tests/rollback_remainder1.py 检查，--apply 才恢复源码。','']
(out/'REPORT.md').write_text('\n'.join(lines));print('report',out/'REPORT.md')

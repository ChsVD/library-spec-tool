import json,csv,statistics,math
from pathlib import Path
root=Path(__file__).resolve().parents[1]
out=root/'evidence/ablation3_20261112_145710'
r=json.loads((out/'results.json').read_text()); vs=['baseline','nonbasic','simple_arith']
by={v:{x['id']:x for x in r if x['variant']==v} for v in vs}
assert all(len(by[v])==52 for v in vs)
lines=['# 第三批优化实验结果','', '每例外部超时400秒；三个配置统一三路并发、绑定CPU 0/2/4。基线固定启用单侧消去和基本零列跳过。性能记录为内核单次耗时，不能把超时计作正常返回。','', '| 配置 | PASS | 超时 | 错误/不匹配 | 完成例耗时和(s) | 最慢完成例(s) |','|---|---:|---:|---:|---:|---:|']
for v in vs:
 xs=list(by[v].values()); ts=[x['kernel_seconds'] for x in xs if x['status']=='PASS']
 lines.append(f"| {v} | {len(ts)} | {sum(x['status']=='TIMEOUT' for x in xs)} | {sum(x['status'] not in ('PASS','TIMEOUT') for x in xs)} | {sum(ts):.3f} | {max(ts):.3f} |")
lines += ['', '## 基线最慢的六例', '', '| 样例 | baseline(s) | nonbasic(s) | simple_arith(s) |','|---|---:|---:|---:|']
for x in sorted(by['baseline'].values(),key=lambda x: x['kernel_seconds'] if x['kernel_seconds'] is not None else 400,reverse=True)[:6]:
 vals=[f"{by[v][x['id']]['kernel_seconds']:.3f}" if by[v][x['id']]['status']=='PASS' else by[v][x['id']]['status'] for v in vs]
 lines.append('| '+x['id']+' | '+' | '.join(vals)+' |')
with (out/'comparison.csv').open('w',newline='') as f:
 w=csv.writer(f);w.writerow(['id']+[v+k for v in vs for k in ['_status','_seconds']])
 for name in sorted(by['baseline']):w.writerow([name]+[by[v][name][k] for v in vs for k in ['status','kernel_seconds']])
s=out/'serial_records.json'
if s.exists():
 rr=json.loads(s.read_text());ids=list(dict.fromkeys(x['id'] for x in rr))
 lines += ['', '## 同CPU串行重复', '', '52例批量运行结束后，10个代表例在CPU 0串行运行，各配置3次并轮换顺序。下表为内核时间中位数；加速比为 baseline/优化版本，大于1表示更快。', '', '| 样例 | baseline(s) | nonbasic(s) | simple_arith(s) | nonbasic加速比 | simple_arith加速比 |','|---|---:|---:|---:|---:|---:|']
 ratios={v:[] for v in vs[1:]}
 for name in ids:
  med={v:statistics.median(x['kernel_seconds'] for x in rr if x['id']==name and x['variant']==v) for v in vs}
  for v in vs[1:]:ratios[v].append(med['baseline']/med[v])
  lines.append('| '+name+' | '+' | '.join(f'{med[v]:.6f}' for v in vs)+' | '+' | '.join(f"{med['baseline']/med[v]:.3f}" for v in vs[1:])+' |')
 lines += ['', '10例等权几何平均加速比：'+ '，'.join(f'{v}={math.exp(statistics.mean(math.log(x) for x in ratios[v])):.3f}' for v in vs[1:])+'。极短例易受测量噪声影响，不能只凭此均值判断大例收益。']
lines += ['', '## 结论', '', '本轮52例完成时间总和：非基遍历比基线减少约1.85%，简单算术减少约1.13%。最慢例分别减少约2.47%和1.90%。大例只有单次样本，收益较小，尚不能视为稳定上界改善。', '', '串行三次中位数中，四个主要中等规模稀疏/稠密例的非基遍历耗时降低约4.3%～5.2%；简单算术基本持平，且有轻微退化。建议优先保留非基遍历作为候选，简单算术继续保持实验选项，暂不固定启用。微秒级样例的差异不作为选择依据。']
lines += ['', '## 验证及边界', '', '各主要配置、两项新优化叠加配置、非基遍历开而跳基本列关的配置，均通过普通及ASan/UBSan验证；每次597例与90次换基恒等式检查。日志在 ../ablation3-validation。输入保持只读；无新增内核运行时验证。', '', '配置、输入和二进制指纹见config.json，源文件指纹见source_hashes.json，每例原始记录与results.json均保留。旧600秒实验的并发度不同，不将跨批次绝对时间变化归因于本次优化。两项新优化叠加尚无52例性能实验。本报告为工程实验，不是形式化证明。']
(out/'REPORT.md').write_text('\n'.join(lines)+'\n')
print('\n'.join(lines))

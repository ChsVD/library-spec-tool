import json,csv,statistics
from pathlib import Path
root=Path(__file__).resolve().parents[1];out=root/'evidence/combined3_20261112_151319';old=root/'evidence/ablation3_20261112_145710'
r=json.loads((old/'results.json').read_text())+json.loads((out/'results.json').read_text())
vs=['baseline','nonbasic','simple_arith','combined'];by={v:{x['id']:x for x in r if x['variant']==v} for v in vs}
assert all(len(by[v])==52 for v in vs)
lines=['# 第三批优化叠加实验','', '日期：2026-11-12。combined同时开启ONE_SIDED、SKIP_BASIC_ZERO、NONBASIC_ITER、SIMPLE_ARITH。生产源码未改动，编译选项默认值不变。', '', '每例外部超时400秒，3路并发，CPU 0/2/4。旧三配置来自ablation3_20261112_145710，combined来自本轮。并发数量相同但任务组合和运行时刻不同，跨批次耗时仅供观察，不能完全归因于优化。', '', '| 配置 | 正确完成 | 超时 | 错误/不匹配 | 内核耗时和(s) | 最慢完成例(s) |','|---|---:|---:|---:|---:|---:|']
for v in vs:
 xs=list(by[v].values());ts=[x['kernel_seconds'] for x in xs if x['status']=='PASS']
 lines.append(f"| {v} | {len(ts)}/52 | {sum(x['status']=='TIMEOUT' for x in xs)} | {sum(x['status'] not in ('PASS','TIMEOUT') for x in xs)} | {sum(ts):.3f} | {max(ts):.3f} |")
lines += ['', '## 基线最慢六例', '', '| 样例 | baseline(s) | nonbasic(s) | simple_arith(s) | combined(s) |','|---|---:|---:|---:|---:|']
for x in sorted(by['baseline'].values(),key=lambda x:x['kernel_seconds'] or 400,reverse=True)[:6]:
 vals=[f"{by[v][x['id']]['kernel_seconds']:.3f}" if by[v][x['id']]['status']=='PASS' else by[v][x['id']]['status'] for v in vs]
 lines.append('| '+x['id']+' | '+' | '.join(vals)+' |')
with (out/'comparison.csv').open('w',newline='') as f:
 w=csv.writer(f);w.writerow(['id']+[v+k for v in vs for k in ['_status','_seconds']])
 for name in sorted(by['baseline']):w.writerow([name]+[by[v][name][k] for v in vs for k in ['status','kernel_seconds']])
rr=json.loads((out/'serial_records.json').read_text());ids=list(dict.fromkeys(x['id'] for x in rr))
assert len(rr)==120
lines += ['', '## 同CPU串行三次复测', '', '在本轮52例结束后，使用四份归档二进制，在CPU 0串行轮换执行10例、各3次。表内是内核时间中位数。这组数据可用于减小批次/并发差异的影响，微秒级案例仍不宜比较百分比。', '', '| 样例 | baseline(s) | nonbasic(s) | simple_arith(s) | combined(s) |','|---|---:|---:|---:|---:|']
for name in ids:
 med={v:statistics.median(x['kernel_seconds'] for x in rr if x['id']==name and x['variant']==v) for v in vs}
 lines.append('| '+name+' | '+' | '.join(f'{med[v]:.6f}' for v in vs)+' |')
lines += ['', '## 结论', '', '叠加配置52例均正确完成，无超时。跨批次观察到总内核时间687.014秒、最长311.538秒；其中后段并发负载下降，不能将相对旧批次的全部下降解释成优化收益。', '', '同CPU串行三次复测的四个主要中等规模案例中，叠加配置均最快：比基线减少约5.3%～9.2%，比仅开启非基遍历减少约1.3%～5.9%。这些样本支持继续保留叠加组合，但不推出所有案例更快或大例上限稳定降至312秒。']
lines += ['', '## 复现和验证', '', '构建命令：`make SX_OPT_ONE_SIDED=1 SX_OPT_SKIP_BASIC_ZERO=1 SX_OPT_NONBASIC_ITER=1 SX_OPT_SIMPLE_ARITH=1 bench`。运行脚本tests/run_combined3.py，串行脚本tests/repeat_combined3.py。', '', '叠加配置已在上一阶段通过597个数学案例、90次换基恒等式测试及ASan/UBSan；生产源码未再修改。日志见../ablation3-validation/one1-skip1-nb1-simple1-san0.log及san1.log。', '', 'config.json、source_hashes.json、comparison_provenance.json记录输入、配置、源码和归档二进制指纹；results.json、serial_records.json和comparison.csv保存数据。工程测试不代替形式化证明。未提交或推送Git。']
(out/'REPORT.md').write_text('\n'.join(lines)+'\n');print('\n'.join(lines))

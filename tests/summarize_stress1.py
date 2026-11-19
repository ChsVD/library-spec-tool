from pathlib import Path
import json,csv,statistics
root=Path(__file__).resolve().parents[1];out=root/'evidence/stress1_20261112_152410';manifest=root/'evidence/stress1_inputs/cases.json'
cases=json.loads(manifest.read_text())['cases'];r=json.loads((out/'results.json').read_text());vs=['baseline','combined'];by={v:{x['id']:x for x in r if x['variant']==v} for v in vs}
assert all(len(by[v])==len(cases) for v in vs)
lines=['# 定向压力测试第一批','', '20个新案例，每例400秒外部进程组超时，原组合基线与四项叠加版共40次运行；四路并发，CPU 0/2/4/6。输入在生成时和实际运行前分别使用Python精确整数/有理数验证证书，标签不来自求解器或FME。', '', '## 覆盖动机', '', '原52例稠密可满足最大n=24、稠密矛盾最大n=16；512位输入仅n=8且为单变量结构。pair-growth和bounded-pairs系列原点可行，无法据其耗时评价大量换基。原随机稠密/稀疏矛盾依赖附加的两条单变量矛盾约束。', '', '新增32变量稠密、16变量混合256位、128变量稀疏、32变量512行相关/冗余、24变量分数薄可行域、48变量稀疏多行矛盾结构；对稠密与薄域增加行列重排，对稠密与256位增加独立种子。', '', '新系统以随机混合线性形式及其相反行构造紧约束，故可行集可能退化为低维甚至单点。这是有意施加的退化压力，不能代表所有有内部点的多面体。矛盾证书使用n+1行的非负整数权重；证书长度不表示最小不可满足子集大小。', '', '## 结果', '', '| 配置 | PASS | TIMEOUT | MISMATCH/ERROR | 完成例内核时间和(s) | 完成例最大RSS(MiB) |','|---|---:|---:|---:|---:|---:|']
for v in vs:
 xs=list(by[v].values());good=[x for x in xs if x['status']=='PASS']
 lines.append(f"| {v} | {len(good)} | {sum(x['status']=='TIMEOUT' for x in xs)} | {sum(x['status'] not in ['PASS','TIMEOUT'] for x in xs)} | {sum(x['kernel_seconds'] for x in good):.3f} | {max(x['peak_rss_kb'] for x in good)/1024:.2f} |")
lines += ['', '超时是性能界限记录，不是正确返回。完成例总和不包含超时，只有完成集合相同时才可直接比较。RSS来自GNU time，包含测试驱动读取和输入副本，并非纯内核峰值；超时强杀进程组时可能没有RSS记录。', '', '| 样例 | n / m | 最大系数位数 | 密度 | baseline(s) | combined(s) |','|---|---:|---:|---:|---:|---:|']
for c in cases:
 vals=[f"{by[v][c['id']]['kernel_seconds']:.4f}" if by[v][c['id']]['status']=='PASS' else by[v][c['id']]['status'] for v in vs]
 lines.append('| '+c['id']+f" | {c['variables']} / {c['rows']} | {c['max_coefficient_bits']} | {c['density']:.3f} | "+' | '.join(vals)+' |')
with (out/'comparison.csv').open('w',newline='') as f:
 w=csv.writer(f);w.writerow(['id','family','n','m','max_bits']+[v+k for v in vs for k in ['_status','_kernel_seconds','_peak_rss_kb']])
 for c in cases:w.writerow([c['id'],c['family'],c['variables'],c['rows'],c['max_coefficient_bits']]+[by[v][c['id']][k] for v in vs for k in ['status','kernel_seconds','peak_rss_kb']])
serial=out/'order_serial_records.json'
if serial.exists():
 rr=json.loads(serial.read_text());assert len(rr)==12
 lines += ['', '## 行列排列的串行三次复测', '', '同CPU、轮换执行顺序，以下为内核时间中位数：', '', '| 输入 | baseline(s) | combined(s) |', '|---|---:|---:|']
 for name in ['dense32-s20261112-unsat','dense32-s20261112-unsat-permuted']:
  med=[statistics.median(x['kernel_seconds'] for x in rr if x['id']==name and x['variant']==v) for v in vs]
  lines.append('| '+name+' | '+' | '.join(f'{x:.4f}' for x in med)+' |')
lines += ['', '## 解释和下一步', '', '共同完成的18例内核耗时总和仅下降约0.4%，256位混合系数组基本持平、部分略慢；单次测量不足以认为这类微小差异显著。128变量稀疏组两配置均超时，现有微优化没有突破此边界。此前组合优势应限定于已测试输入，不能宣称普遍更快。', '', '覆盖核查见../stress1_inputs/coverage_checks.json：所有变量均同时出现正负系数，原点违反29～278条约束，排除了单侧消去与原点直接可行的快路径。', '', '后续优先在测试专用构建中测量换基次数、最大整数位数、活动列非零密度及GCD/乘除耗时，区分路径长度和单步算术成本；再针对128变量组做规模梯度和更多种子，补充有内部点的非退化系统以及真实QCP/SMT导出输入。当前没有增加生产统计或改变选主元策略。']
lines += ['', '## 复现与限制', '', '生成器tests/generate_stress1.py；运行器tests/run_stress1.py；汇总tests/summarize_stress1.py。输入和见证/权重证书在../stress1_inputs，配置、指纹、二进制及每例原始输出在本目录。输入使用少于1024字符的十进制数，满足测试驱动读取范围。', '', '这是定向合成压力集，尚缺真实SMT导出的实例、大量独立种子和大例重复测量。单次并发时间不能证明稳定加速，也不能推广为最坏情况复杂度。未修改求解器源码、默认开关或原52例；无Git提交/推送。']
(out/'REPORT.md').write_text('\n'.join(lines)+'\n');print('\n'.join(lines))

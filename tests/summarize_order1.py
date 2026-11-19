from pathlib import Path
import json,math,statistics,csv,hashlib
root=Path(__file__).resolve().parents[1];out=root/'evidence/order1_20261112_161356';selection=json.loads((out/'selection.json').read_text());selected=selection['selected_order'];doc=json.loads((root/'evidence/order1_inputs/cases.json').read_text());orders=doc['orders']
normal=json.loads((out/'screen_normal/results.json').read_text());profile=json.loads((out/'screen_profile/results.json').read_text());assert len(normal)==len(profile)==544
nd={(x['base_id'],x['order']):x for x in normal};pd={(x['base_id'],x['order']):x for x in profile};geo=lambda xs:math.exp(statistics.mean(math.log(x) for x in xs));cost=lambda x:x['kernel_seconds'] if x['status']=='PASS' else 800.0
lines=['# 输入行列排序实验结果','', '仅离线重排输入，固定四项优化叠加版，生产源码未改动。普通与统计分批运行；4路并发，CPU 0/2/4/6，每例400秒。8种策略包括原顺序、行/列/行列按非零数排序、行/列/行列按最大系数位数排序，以及固定随机对照。全部升序、稳定同分，定义见项目ORDERING1.md。', '', '## 正确性与测量范围', '', '48随机例＋20真实QCP回归子问题，共68例×8顺序=544条逻辑记录；同一原例中相同输入哈希共用一次执行，每阶段实际355次。普通/统计各自544条记录均须按PASS/TIMEOUT/ERROR区分，重复别名不是独立样本。', '', '| 阶段 | PASS逻辑记录 | TIMEOUT | 错误/不匹配 |','|---|---:|---:|---:|']
for name,rr in [('普通',normal),('统计',profile)]:lines.append(f"| {name} | {sum(x['status']=='PASS' for x in rr)} | {sum(x['status']=='TIMEOUT' for x in rr)} | {sum(x['status'] not in ['PASS','TIMEOUT'] for x in rr)} |")
lines += ['', '所有重排逐项验证与原矩阵的排列关系，并复核同步排列后的精确见证/整数权重证书。常数列不动，不改变不等号或数值。20个QCP子问题只用于兼容性，不参与性能选优。', '', '## 预先指定的训练/留出评估', '', '前4种子24例训练，后4种子24例留出。只根据训练集PAR2相对原顺序代价比的几何平均选择候选；超时代价800秒；原顺序和六个排序参与选择，随机对照不参与。以下比值小于1表示更快。', '', '| 顺序 | 训练相对耗时 | 留出相对耗时 | 留出最差耗时比 | 留出相对换基次数(几何平均) |','|---|---:|---:|---:|---:|']
for order in orders:
 ratios={};counts={}
 for split in ['train','holdout']:
  ids=sorted({x['base_id'] for x in normal if x['split']==split});ratios[split]=[cost(nd[n,order])/cost(nd[n,'identity']) for n in ids]
  if split=='holdout':counts=[pd[n,order]['profile']['completed']/pd[n,'identity']['profile']['completed'] for n in ids]
 lines.append(f"| {order} | {geo(ratios['train']):.4f} | {geo(ratios['holdout']):.4f} | {max(ratios['holdout']):.3f} | {geo(counts):.4f} |")
lines += ['', f'训练规则选中 **{selected}**。未根据留出结果换候选。训练优势未转化为可靠的留出整体优势：不能据此把该规则固定到生产。位数行排序整体偏慢；列排序的收益也较小、依赖样例。', '', '普通时间是内核时间，不含离线Python排序。该时间不代表未来C版排序的端到端收益。单次并发测量中的百分之几差异应谨慎解释；较大差异另由换基次数与串行复测交叉检查。', '', '## 两个对照案例', '', '| 输入 | 顺序 | 普通内核时间(s) | 换基次数 | 峰值表整数位数 |','|---|---|---:|---:|---:|']
for n in ['interior32-s31005-feas','interior32-s31006-unsat']:
 for order in ['identity',selected]:
  x=nd[n,order];a=pd[n,order]['profile'];lines.append(f"| {n} | {order} | {x['kernel_seconds']:.4f} | {a['completed']} | {a['peak_table_bits']} |")
serial=json.loads((out/'serial_results.json').read_text());assert len(serial)==12
lines += ['', '上述为留出集事后挑选的最大收益/最大退化案例，只解释机制，不作为新一轮选优证据。同CPU串行各3次、轮换顺序，中位数如下：', '', '| 输入 | 原顺序(s) | 所选排序(s) | 耗时比 |','|---|---:|---:|---:|']
for name in dict.fromkeys(x['base_id'] for x in serial):
 a=statistics.median(x['kernel_seconds'] for x in serial if x['base_id']==name and x['order']=='identity');b=statistics.median(x['kernel_seconds'] for x in serial if x['base_id']==name and x['order']==selected);lines.append(f'| {name} | {a:.4f} | {b:.4f} | {b/a:.3f} |')
lines += ['', '## 128变量压力例', '', '保持训练阶段选中的候选，与原顺序直接对照；不再按大例结果改选。普通阶段用于完成/超时与计时，统计阶段的部分计数不代表最终求解结果。', '', '| 输入 | 顺序 | 普通结果/秒 | 统计结果 | 最后记录的完成换基 | 峰值表位数 | 峰值密度 |','|---|---|---:|---|---:|---:|---:|']
hn=json.loads((out/'hard_normal/results.json').read_text());hp=json.loads((out/'hard_profile/results.json').read_text());hd={(x['base_id'],x['order']):x for x in hp}
for x in sorted(hn,key=lambda x:(x['base_id'],x['order'])):
 p=hd[x['base_id'],x['order']];a=p['profile'];value=f"{x['kernel_seconds']:.3f}" if x['status']=='PASS' else x['status'];lines.append(f"| {x['base_id']} | {x['order']} | {value} | {p['status']} | {a['completed']} | {a['peak_table_bits']} | {a['peak_density']:.1%} |")
lines += ['', '在已输出的超时前观测区间内，候选的峰值位数和密度较低，但换基过程仍未结束。超时前完成换基较多，只说明执行了更多步骤，不表示距离最终结果更近；不能用这些部分统计替代完成时间。']
lines += ['', '## 解释与范围', '', '排序没有改变基本的数学算法，但改变了最小稳定编号策略所看到的行列编号，因此可能极大改变换基轨迹。输入初始更稀疏的位置不等于后续更少换基或更小整数。当前证据支持继续保持默认原顺序，而不是统一启用某个粗粒度排序。是否按结构选择排序，需新增独立样例验证，不能从这批结果直接拟合规则并声称普遍提速。', '', '记录源文件、输入、排列与证书、二进制指纹，数据见screen_normal、screen_profile、hard_normal、hard_profile及serial_results.json。训练选择见selection.json。输入/证书在../order1_inputs。未修改原QCP环境、算法源码或Makefile，无提交/推送。']
(out/'REPORT.md').write_text('\n'.join(lines)+'\n')
with (out/'comparison.csv').open('w',newline='') as f:
 w=csv.writer(f);w.writerow(['base_id','split','order','status','seconds','measured_id','pivots','peak_table_bits','peak_density'])
 for x in sorted(normal,key=lambda x:(x['base_id'],x['order'])):
  p=pd[x['base_id'],x['order']]['profile'];w.writerow([x['base_id'],x['split'],x['order'],x['status'],x['kernel_seconds'],x['measured_id'],p['completed'],p['peak_table_bits'],p['peak_density']])
config=json.loads((out/'config.json').read_text());assert all(hashlib.sha256((root/n).read_bytes()).hexdigest()==h for n,h in config['production_sha256'].items())
print('\n'.join(lines))

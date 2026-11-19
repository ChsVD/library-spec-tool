from pathlib import Path
import json,csv,statistics,hashlib
root=Path(__file__).resolve().parents[1];out=root/'evidence/profile1_20261112_155628'
pr=json.loads((out/'results.json').read_text());seed=root/'evidence/seed2_20261112_160424';sr=json.loads((seed/'results.json').read_text());sp=root/'evidence/seed2_profile_20261112_160549';spr=json.loads((sp/'results.json').read_text());qp=root/'evidence/qcp1_profile_20261112_160549';qr=json.loads((qp/'results.json').read_text());qrun=root/'evidence/qcp1_20261112_160423'
assert len(pr)==14 and len(sr)==96 and len(spr)==48 and len(qr)==20
assert all(x['status']=='PASS' and x['profile']['stage']=='final' for x in spr+qr)
lines=['# 测试统计、QCP调用与多种子实验报告','', '日期：2026-11-12。只添加默认关闭的测试统计，未实施新的算法优化；每例外部400秒上限。普通计时与统计诊断分批运行，不混用耗时。', '', '## 可关闭性与验证', '', 'SX_PROFILE=0：两种性能配置的预处理token、可执行文件.text均与修改前归档一致，普通库不含统计符号。快照/差异/指纹位于../profile1_baseline。SX_PROFILE=1：独立构建目录，597数学案例及90换基恒等式测试通过，叠加版ASan/UBSan通过；已知一次换基、连续调用计数重置和密度范围检查通过。', '', '恢复方式：`python3 tests/rollback_profile1.py`先检查，`--apply`恢复两份原始文件；如果有后续修改则拒绝覆盖。不会重置工作树或删除历史实验。', '', '## 7例热点诊断', '', '原组合基线与四项叠加各7例：均5例正常返回、2例超时，无错误答案。以下显示叠加版。超时行是最后一次已输出的部分观测，不是最终结果。', '', '| 输入 | 状态 | 完成换基 | 初始/峰值表位数 | 算术输出峰值位数 | 初始/峰值非基密度 |','|---|---|---:|---:|---:|---:|']
for x in sorted((x for x in pr if x['variant']=='combined'),key=lambda x:x['id']):
 a=x['profile'];lines.append(f"| {x['id']} | {x['status']} | {a['completed']} | {a['initial_bits']} / {a['peak_table_bits']} | {a['arithmetic_bits']} | {a['initial_density']:.1%} / {a['peak_density']:.1%} |")
lines += ['', '| 输入 | GCD(s) | 乘法(s) | 精确除法(s) | addmul(s) | 统计运行已观测时间(s) |','|---|---:|---:|---:|---:|---:|']
for x in sorted((x for x in pr if x['variant']=='combined'),key=lambda x:x['id']):
 a=x['profile'];lines.append('| '+x['id']+' | '+' | '.join(f'{z:.3f}' for z in a['seconds'])+f" | {a['elapsed']:.3f} |")
lines += ['', '四个计时桶仅包装内核直接调用，彼此不重叠；GCD内部算术包含于GCD，addmul内部乘法包含于addmul，不重复记入乘法。位数最大值不包括后端内部未暴露的临时对象。统计扫描和时钟会扰动执行，表中秒数用于定位热点，不能与正式计时直接算加速比。', '', '密度定义为非基列A中非零数/(行数×非基列数)。每次完整换基扫描表；算术进度中的密度和表位数来自最后一次完成换基。超时统计可能落后于强杀时刻数秒。', '', '关键观察：128变量输入从约4%密度变为约77%～79%峰值，表位数约950位、算术结果约1900位，完成1300余至1400余次换基仍未结束。GCD与精确除法合计约57%的已观测时间，乘法和addmul也很重。混合256位案例表位数涨到4106、算术结果8207，GCD与精确除法合计约70%。', '', '同一稠密矛盾例重排行列使换基次数1003→754；两配置各自次数相同，说明此次微优化没有改变修复路径。冗余组的普通乘法调用从1293870降到420237、addmul从1255815降到384647，因此零项优化在这类结构上更有效；大整数混合组减少调用的比例小，解释了整体收益有限。', '', '## 48例、8个新种子的正式性能', '', '8种子×3类×可满足/矛盾，共48例。两配置各48/48正确，零超时；所有标签由精确见证/非负整数权重独立复核。有内部点组的可满足输入在构造点具有严格正余量，补充上一批大量紧约束退化系统的偏差。', '', '| 类型 | 每配置例数 | baseline内核时间和(s) | combined内核时间和(s) | 耗时减少 |','|---|---:|---:|---:|---:|']
for family in sorted({x['family'] for x in sr}):
 xs={v:[x for x in sr if x['family']==family and x['variant']==v] for v in ['baseline','combined']};ts={v:sum(x['kernel_seconds'] for x in a) for v,a in xs.items()};lines.append(f"| {family} | {len(xs['baseline'])} | {ts['baseline']:.3f} | {ts['combined']:.3f} | {1-ts['combined']/ts['baseline']:.2%} |")
lines += ['', '上述为每例单次、四路并发配对运行；0.4%级差异不应当作显著提升。统计版另行跑完同48例，无错误；以下为不同种子的诊断范围：', '', '| 类型 | 换基次数范围 | 峰值表位数范围 | 峰值非基密度范围 |','|---|---:|---:|---:|']
for family in sorted({x['family'] for x in spr}):
 a=[x['profile'] for x in spr if x['family']==family];lines.append(f"| {family} | {min(x['completed'] for x in a)}–{max(x['completed'] for x in a)} | {min(x['peak_table_bits'] for x in a)}–{max(x['peak_table_bits'] for x in a)} | {min(x['peak_density'] for x in a):.1%}–{max(x['peak_density'] for x in a):.1%} |")
lines += ['', '## 真实QCP分支调用', '', '来源为本机smt_solver仓库smt_qcp分支提交3098d53575ad2a99f9f561ec4e10233c98f44fd3的既有归档，隔离副本仅加捕获钩子。48个原SMT回归用例全部按原预期结束，捕获121次消元前理论调用，去重得到20个线性子问题，全部导出无排除；最多4变量13行。', '', '导出时拆等式、代入固定INT*_MAX、删全零列并保留映射；支持整数严格关系加1规范化，但这批实际捕获已无严格行。标签来自独立Python精确消元生成的证书再复核，不能拿完整SMT答案代替子问题的有理答案。此为整数分支的有理松弛输入，不是完整SMT求解实验。', '', f"两正式配置均20/20正确；统计叠加版20/20正确，换基次数范围{min(x['profile']['completed'] for x in qr)}–{max(x['profile']['completed'] for x in qr)}，峰值表位数最大{max(x['profile']['peak_table_bits'] for x in qr)}。它们支持实际路径兼容性，但规模太小，不能代替生产规模压力测试。", '', '## 下一步优先级', '', '1. 先做小规模的行列排序实验，原求解策略不动，仅在测试输入中按稀疏度/系数位数排序并保留映射。已有1003→754换基的证据表明路径选择可能比逐项微优化更有价值，但不能据此保证某个排序普遍更快。', '2. 聚焦GCD与精确除法的实现/调用方式，在项目MiniGMP范围内做剖析与独立微基准；首先区分行规范化与消元乘数约简的成本，避免盲目降低约简频率导致整数进一步膨胀。', '3. 后续再考虑选主元代价（稀疏度、系数位数）或结构分解。选主元变化涉及终止性/防循环论证，不能把当前稳定编号规则随意替换。输入很快变稠密，也不支持立即改成全程稀疏表。', '', '本轮没有改排序、选主元、GCD策略或后端算法。未完成形式化验证；无提交或推送。', '', '## 证据位置', '', '- 当前目录：7例统计原始JSON、stderr进度、归档二进制、配置和源码指纹。', '- ../seed2_20261112_160424：48例正式性能；../seed2_profile_20261112_160549：统计。', '- ../qcp1_20261112_160423：20例正式运行；../qcp1_profile_20261112_160549：统计。', '- ../qcp_capture1：上游出处、原始输入与调用、捕获补丁、构建和运行日志。', '- ../seed2_inputs、../qcp1_inputs：输入及独立数学证书。', '- 项目PROFILE_TESTING.md：统计口径、构建及回退说明。']
(out/'REPORT.md').write_text('\n'.join(lines)+'\n')
with (out/'profile_summary.csv').open('w',newline='') as f:
 w=csv.writer(f);w.writerow(['id','variant','status','pivots','initial_bits','peak_table_bits','arithmetic_bits','initial_density','peak_density','gcd_seconds','mul_seconds','div_seconds','addmul_seconds'])
 for x in pr:
  a=x['profile'];w.writerow([x['id'],x['variant'],x['status']]+[a[k] for k in ['completed','initial_bits','peak_table_bits','arithmetic_bits','initial_density','peak_density']]+a['seconds'])
for directory,records in [(seed,sr),(qrun,json.loads((qrun/'results.json').read_text()))]:
 with (directory/'comparison.csv').open('w',newline='') as f:
  w=csv.writer(f);w.writerow(['id','variant','status','kernel_seconds','peak_rss_kb'])
  for x in records:w.writerow([x[k] for k in ['id','variant','status','kernel_seconds','peak_rss_kb']])
print('\n'.join(lines))

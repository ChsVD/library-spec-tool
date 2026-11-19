from pathlib import Path
import json,csv,statistics,hashlib
root=Path(__file__).resolve().parents[1];out=root/'evidence/profile2_20261112_164317';r=json.loads((out/'results.json').read_text());micro=json.loads((out/'micro_results.json').read_text());samples=json.loads((out/'micro_samples.json').read_text())
lines=['# GCD与精确除法热点细分','', '2026-11-12。仅扩展SX_PROFILE测试统计，默认关闭，生产算法和MiniGMP均未修改。7个代表例，5例正常正确返回、2例400秒超时。超时统计为最后输出时刻的部分观测。', '', '## 阶段成本', '', '将直接GCD和精确除法调用划分为行规范化(normalize)与消元乘数约简。时间不包含乘法/addmul；比例的分母仅为GCD＋精确除法，不是整个内核。', '', '| 案例 | 状态 | 规范化GCD(s) | 规范化除法(s) | 乘数约简GCD(s) | 乘数约简除法(s) | 规范化占这两类算术时间 |','|---|---|---:|---:|---:|---:|---:|']
for x in sorted(r,key=lambda x:x['id']):
 a=x['profile'];s=a['phase_seconds'];total=sum(map(sum,s));lines.append(f"| {x['id']} | {x['status']} | {s[0][0]:.3f} | {s[0][1]:.3f} | {s[1][0]:.3f} | {s[1][1]:.3f} | {sum(s[0])/total:.2%} |")
lines += ['', '| 案例 | 规范化GCD次数 | GCD保持原因子比例 | 全部精确除法中除数为1比例 | 商绝对值为1比例 |','|---|---:|---:|---:|---:|']
for x in sorted(r,key=lambda x:x['id']):
 a=x['profile'];lines.append(f"| {x['id']} | {a['phase_calls'][0][0]} | {a['gcd_kept'][0]/a['phase_calls'][0][0]:.2%} | {sum(a['div_one'])/a['calls'][2]:.2%} | {sum(a['quotient_one'])/a['calls'][2]:.2%} |")
lines += ['', '规范化占GCD＋精确除法成本约84%～95%。大例中约95%～97%的规范化GCD返回传入的已有因子，说明重复确认系数可被当前因子整除占用了大量调用；计数比例不等于耗时比例，本轮未按该返回分类分别计时。除数1和商1的快路径虽可便宜实现，但在大例中出现比例很低。', '', '## 源码核实', '', 'vendor/gmp/minigmp/mpz_divexact.c直接调用mpz_div_qr(...,GMP_DIV_TRUNC)，是通用除法入口。mpz_div_qr对非零且长度足够的输入分配临时余数对象，要求商时还分配临时商对象，然后调用mpn_div_qr。', '', 'mpz_gcd.c为两个非零输入创建临时整数、取绝对值和提取2的因子，再做余数与二进制GCD过程。因此“GCD不变”仍可能承担准备和分配成本。此次只读取后端文件，没有改写。', '', '## 真实操作数回放微基准', '', f"捕获{samples['captured']}条操作数记录，去重{samples['unique']}组。按阶段、操作、位数桶及结果类别最多选4组，共{len(micro)-7}组真实样本，另加7组边界控制。所有捕获结果均由Python精确gcd或整除复核；微基准的原实现与候选实现逐项验证结果及输入不变。", '', 'GCD候选：r=b mod a；r=0则返回abs(a)，否则gcd(a,r)。此处a为当前正因子，a>0由调用位置保证。整数恒等式gcd(a,b)=gcd(a,b mod a)使结果与原写法相同；余数为负也可交给原GCD取绝对值。候选只在测试程序中。', '', '精确除法候选：除数±1时复制/取负，分子分母绝对值相等时返回±1，否则调用原mpz_divexact。没有实现新的通用除法算法。', '', '同CPU串行、5次交替顺序，native批次自适应到至少3毫秒，两实现使用相同迭代次数。下表加速比为native/candidate，大于1更快，是逐样本中位耗时比的中位数：', '', '| 阶段 | 操作 | 样本类别 | 数量 | 加速比中位数 | 最小–最大 |','|---|---|---|---:|---:|---:|']
for phase in [0,1]:
 for op in [0,1]:
  for kind in sorted({x['kind'] for x in micro if x['phase']==phase and x['operation']==op}):
   ss=[x['speedup'] for x in micro if x['phase']==phase and x['operation']==op and x['kind']==kind];lines.append(f"| {['规范化','乘数约简'][phase]} | {['GCD','精确除法'][op]} | {kind} | {len(ss)} | {statistics.median(ss):.3f} | {min(ss):.3f}–{max(ss):.3f} |")
lines += ['', 'kept表示GCD等于第一个输入因子，one表示结果1且非kept；den_one表示除数绝对值1，quotient_one表示商绝对值1且非den_one。other为其余情况。', '', '这些是按类别选取、缓存较热的固定操作数微基准，不按真实调用频率或耗时加权，不代表整个求解器的加速比。规范化kept组中位加速约1.42倍，但因子变化组通常略慢；需要整套求解对照才能确认净收益。20多倍的单位除法微基准加速不能直接解释成明显的整体提升。', '', '## 建议的下一项独立实验', '', '优先：仅在行规范化中试验“余数优先GCD”，做成默认关闭的编译选项。保留完整正GCD约简，复用行级临时整数，避免每个系数创建新的项目对象。通过余数为零保持已有因子，否则调用原GCD，数学覆盖不减少。', '', '下一轮统计需把新增余数耗时单列，不能只看GCD时间减少。先用原52例、扩展种子和混合大整数案例验证，再以关闭统计的构建做整套消融；同时监测因子变化较多的案例是否退化。不要把此策略直接推广到所有GCD调用。', '', '单位精确除法可留作另一个小实验，但按当前大例调用比例，优先级较低。若上述实验收益不足，再分析同一行共享除数时的准备/分配成本；不应直接降低GCD约简频率，以免中间整数膨胀。', '', '本轮没有把任何候选写法接入求解器，也未宣称已获得端到端提速。', '', '## 验证、回退和文件', '', '普通与统计构建各通过597案例及90换基恒等式；统计构建ASan/UBSan通过。170组微基准全部正确，微基准ASan/UBSan通过。各阶段调用计数与总计精确相加；正常返回时乘数约简的除法调用数为GCD的两倍。', '', 'SX_PROFILE=0预处理token及普通可执行文件.text与上阶段相同。快照、补丁与指纹在../profile2_baseline。`python3 tests/rollback_profile2.py`只检查；加`--apply`回到第一版统计；加`--apply --all`恢复最初无统计的solver.c/Makefile。若有后续修改则拒绝覆盖。历史profile1快照未改写。', '', '本目录保留结果、原始stderr操作数、micro_samples.json、micro_results.json、micro_raw.json、计时配置、独立校验与sanitizer日志。生产源码仅新增受SX_PROFILE保护的规范化阶段钩子，测试实现位于tests/profile.c。未提交或推送。']
(out/'REPORT.md').write_text('\n'.join(lines)+'\n')
with (out/'phase_summary.csv').open('w',newline='') as f:
 w=csv.writer(f);w.writerow(['id','status','normalize_gcd_seconds','normalize_div_seconds','pivot_gcd_seconds','pivot_div_seconds','normalize_gcd_calls','normalize_gcd_kept'])
 for x in r:
  a=x['profile'];w.writerow([x['id'],x['status']]+a['phase_seconds'][0]+a['phase_seconds'][1]+[a['phase_calls'][0][0],a['gcd_kept'][0]])
print('\n'.join(lines))

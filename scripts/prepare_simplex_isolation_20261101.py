from pathlib import Path
import hashlib
import json
import shutil
import subprocess

projects = Path('/home/maxu/Projects')
tool = projects / 'library-spec-tool'
root = tool / 'runs/isolated-simplex-20261101-01'
if root.exists():
    raise SystemExit('Refusing to overwrite existing experiment: ' + str(root))
root.mkdir()
ignore = shutil.ignore_patterns('.git', '_build', '.venv', '__pycache__', '.pytest_cache', '*.pyc')
def copy(src, dst):
    shutil.copytree(src, dst, ignore=ignore, symlinks=False)
def revision(path):
    p = subprocess.run(['git', '-C', str(path), 'rev-parse', 'HEAD'], capture_output=True, text=True)
    return p.stdout.strip() if p.returncode == 0 else None
for name in ['target', 'references', 'contracts', 'generated', 'checks', 'logs', 'evaluation', 'scripts']:
    (root/name).mkdir()
qcp = projects/'qcp-v2.2.0'
copy(qcp, root/'qcp')
copy(qcp/'QCP_examples/Applications_human/simplex', root/'target/simplex-baseline')
copy(qcp/'QCP_examples/Applications_human/fme', root/'references/fme/QCP_examples')
copy(qcp/'Rocq/examples/Applications_human/fme', root/'references/fme/Rocq')
yices = projects/'yices2'
copy(yices/'src', root/'references/yices2/src')
copy(yices/'doc', root/'references/yices2/doc')
for name in ['LICENSE', 'README.md']:
    if (yices/name).exists(): shutil.copy2(yices/name, root/'references/yices2'/name)
smt = Path('/mnt/c/Users/24123/.codex/tmp/smt-inspection-20261030/smt_solver')
if not smt.exists(): raise RuntimeError('Original SMT source missing')
copy(smt, root/'references/smt_solver')
(root/'spec-tool').mkdir()
for name in ['stage1','stage2','stage3','stage4','scripts','templates','tests']:
    copy(tool/name, root/'spec-tool'/name)
for p in tool.iterdir():
    if p.is_file() and p.suffix in ['.md','.toml','.json']:
        shutil.copy2(p, root/'spec-tool'/p.name)
(root/'spec-tool/input').mkdir()
(root/'spec-tool/runs').mkdir()
(root/'spec-tool/input/README.txt').write_text('本轮输入见环境根目录 INPUT_MANIFEST.json。尚未运行模块分析或生成规约。\n', encoding='utf-8')
manifest = {
 'root': str(root), 'created_date': '2026-11-01',
 'status': 'prepared_not_spec_generated_or_proved',
 'target_baseline': 'target/simplex-baseline',
 'target_working': 'qcp/QCP_examples/Applications_human/simplex',
 'qcp_root': 'qcp', 'spec_tool_root': 'spec-tool',
 'references': {'proved_fme_c': 'references/fme/QCP_examples', 'proved_fme_coq': 'references/fme/Rocq',
                'algorithm_only_yices': 'references/yices2', 'original_smt': 'references/smt_solver'},
 'revisions': {'qcp': revision(qcp), 'yices2': revision(yices), 'original_smt': revision(smt), 'spec_tool': revision(tool)},
 'reference_status': 'FME proof sources copied, not recompiled. Yices and original SMT are algorithm/source references, not certified implementations.',
 'isolation': 'Independent file copies; host compilers shared. No shared .venv or _build. Not a container.',
 'input_scope': 'Non-strict linear inequalities; rational feasibility and sound integer-unsat conclusion. No integer-SAT guarantee.',
 'outputs': ['contracts','generated','checks','logs','evaluation'],
 'runtime_configuration': 'Inspect copied spec-tool entrypoints before execution; this manifest is an experiment inventory, not a claimed CLI config.'
}
(root/'INPUT_MANIFEST.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2)+'\n')
hashes = {}
for dirname in ['target', 'references', 'spec-tool']:
    for p in sorted((root/dirname).rglob('*')):
        if p.is_file(): hashes[str(p.relative_to(root))] = hashlib.sha256(p.read_bytes()).hexdigest()
for p in sorted((root/'qcp').rglob('*')):
    if p.is_file(): hashes[str(p.relative_to(root))] = hashlib.sha256(p.read_bytes()).hexdigest()
(root/'SOURCE_MANIFEST.json').write_text(json.dumps(hashes, indent=2)+'\n')
versions = {}
for name, cmd in [('coq',['/home/maxu/.opam/4.14.1/bin/coqc','--version']),('python',['python3','--version']),('gcc',['gcc','--version']),('dune',['/home/maxu/.opam/4.14.1/bin/dune','--version'])]:
    p = subprocess.run(cmd, capture_output=True, text=True)
    versions[name] = {'argv':cmd,'exit_code':p.returncode,'output':p.stdout+p.stderr}
(root/'TOOLCHAIN.json').write_text(json.dumps(versions, indent=2)+'\n')
p = subprocess.run(['python3', str(root/'qcp/QCP_examples/Applications_human/simplex/tests/test_simplex.py')], capture_output=True, text=True)
(root/'checks/simplex-baseline-test.log').write_text(p.stdout+p.stderr)
if p.returncode: raise RuntimeError('Isolated baseline tests failed')
(root/'README.txt').write_text('''单纯形 spec-tool 隔离实验（2026-11-01）

目录沿用此前 BN 实验：qcp、target、references、contracts、generated、checks、logs、evaluation。
新增 spec-tool 为工具代码快照，其 input 和 runs 为本轮独立目录。
运行前需根据实际阶段入口配置输入；INPUT_MANIFEST.json 是材料清单，不是工具 CLI 配置。

target/simplex-baseline：初始源码与测试快照，后续不修改。
qcp/QCP_examples/Applications_human/simplex：后续适配、规约和证明使用的工作源码。
references/fme：已存在的 FME C 规约与 Coq 文件，本次未重编译证明。
references/yices2：Yices 的 src、doc 和许可/说明，只作算法参考。
references/smt_solver：原始 SMT 源码参考。
contracts：自然语言及形式化规约输出。
generated：新生成的通用定义、引理及其他中间产物。
qcp/Rocq/examples：后续实际证明文件应按 QCP 要求放在这里。
checks、logs、evaluation：检查记录、执行日志、实验统计。

所有上述材料都是独立文件副本。宿主 Python、GCC、Coq 和 dune 共享；
未复制 Git 历史、Python 虚拟环境和 dune 构建缓存，不声称完全离线可运行。
需要 Python 依赖或重建 QCP 时，在本副本中完成。
进入证明阶段应遵循 qcp/AGENTS.md 和其中指定的 verification-orchestrator。
本次仅准备环境并复跑 C 测试，未运行 spec-tool 模型任务、未生成规约或开始证明。
不将 Yices 或原始 SMT 源码视为已证明参考库。

测试结果：checks/simplex-baseline-test.log；编译器版本：TOOLCHAIN.json。
来源及路径：INPUT_MANIFEST.json；初始文件 SHA256：SOURCE_MANIFEST.json。
后续写入文件须使用本环境内路径，不使用以前 BN 实验的绝对路径。
''', encoding='utf-8')
print(root)
print('Hashed files:', len(hashes))
print(p.stdout)

"""Pinned backend discovery and logged subprocess execution."""
import os
import shutil
import signal
import subprocess
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
FM_COMMIT = "c552cd5ef25bd096178c7b06d3645dc3fd1e376e"
CODEGRAPH_VERSION = "1.6.2-fmagent.1"


def checked(argv, cwd, log, env=None, timeout=600):
    with Path(log).open("w") as stream:
        process = subprocess.Popen([str(a) for a in argv], cwd=cwd, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=timeout)
        except (subprocess.TimeoutExpired, KeyboardInterrupt):
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise RuntimeError("Graph analysis interrupted/timed out; see " + str(log))
        if code:
            raise RuntimeError(f"Graph analysis failed (exit {code}); see {log}")


def environment(deps_root=BASE):
    fm = deps_root / ".deps/FM-Agent"
    python = deps_root / ".venv-graph/bin/python"
    cg = deps_root / ".deps/codegraph/bin/codegraph"
    if not all(p.exists() for p in (fm, python, cg)) or not shutil.which("clang"):
        raise RuntimeError("FM-Agent graph environment missing; run bash scripts/setup_graph.sh inside WSL")
    commit = subprocess.check_output(["git", "-C", str(fm), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", str(fm), "status", "--porcelain", "--untracked-files=no"], text=True).strip()
    version = subprocess.check_output([str(cg), "--version"], text=True).strip()
    if commit != FM_COMMIT or dirty or version != CODEGRAPH_VERSION:
        raise RuntimeError("FM-Agent/CodeGraph differs from the pinned graph backend")
    return fm, python, cg



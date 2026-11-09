#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
FM_COMMIT=c552cd5ef25bd096178c7b06d3645dc3fd1e376e
if ! command -v clang >/dev/null || ! command -v rg >/dev/null || ! command -v git >/dev/null || ! command -v make >/dev/null || ! command -v perl >/dev/null; then
  sudo apt-get update
  sudo apt-get install -y clang ripgrep git python3-venv make perl
fi
export CODEGRAPH_TELEMETRY=0
mkdir -p .deps
if [ ! -d .deps/FM-Agent ]; then
  git clone https://github.com/fmagent-project/FM-Agent.git .deps/FM-Agent
  git -C .deps/FM-Agent checkout --detach "$FM_COMMIT"
fi
test "$(git -C .deps/FM-Agent rev-parse HEAD)" = "$FM_COMMIT"
test -z "$(git -C .deps/FM-Agent status --porcelain --untracked-files=no)"
if command -v uv >/dev/null; then
  test -x .venv-graph/bin/python || uv venv .venv-graph --python python3
  uv pip install --python .venv-graph/bin/python -r scripts/graph-requirements.txt
else
  test -x .venv-graph/bin/python || python3 -m venv .venv-graph
  .venv-graph/bin/python -m pip install -r scripts/graph-requirements.txt
fi
export FM_AGENT_CODEGRAPH_DIR="$PWD/.deps/codegraph"
export CODEGRAPH_TELEMETRY=0
ROOT="$PWD"
(cd .deps/FM-Agent && "$ROOT/.venv-graph/bin/python" -c 'from src.languages.codegraph import _codegraph_cmd; print(_codegraph_cmd())')
python3 -c 'from stage2.fm_graph import environment; print(environment())'
clang --version

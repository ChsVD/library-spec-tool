"""Build a call graph and determine the stage-two scope."""
import argparse
import json
import subprocess

from .backend import BASE
from .pipeline import analyze


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", required=True, help="target source directory")
    parser.add_argument("--compile-commands", required=True)
    parser.add_argument("--configuration", required=True, help="platform, architecture and build configuration")
    parser.add_argument("--entry", action="append", default=[], help="repeatable: name, relative-file:name, or function ID")
    parser.add_argument("--reuse-libraries", help="JSON array declaring proven reuse libraries")
    parser.add_argument("--output", required=True, help="new run directory")
    parser.add_argument("--deps-root", default=BASE, help="directory with pinned .deps and .venv-graph")
    args = parser.parse_args(argv)
    try:
        result = analyze(target=args.target, compile_commands=args.compile_commands,
                         configuration=args.configuration, entries=args.entry, reuse_libraries=args.reuse_libraries,
                         output=args.output, deps_root=args.deps_root)
    except (KeyError, TypeError, ValueError, OSError, RuntimeError, subprocess.SubprocessError) as exc:
        parser.exit(1, f"stage1: {exc}\n")
    print(json.dumps({"status": result["status"], "functions": len(result["scope"]["function_ids"])}))
    return 2 if result["status"] == "partial_analysis" else 0


if __name__ == "__main__":
    raise SystemExit(main())

"""Generate natural-language contracts from a v2 stage-one run."""
import argparse
import json

from .codex_backend import CodexModel
from .pipeline import run
from .contract_store import DEFAULT_ROOT


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage1", required=True, help="stage1.json")
    parser.add_argument("--output", required=True)
    parser.add_argument("--reuse-contracts", help="JSON mapping of reuse function IDs to contract intervals")
    parser.add_argument("--background", action="append", default=[], help="repeatable path to supporting materials")
    parser.add_argument("--contract-store", default=DEFAULT_ROOT, help="shared builtin contracts directory")
    parser.add_argument("--model")
    parser.add_argument("--reasoning-effort", choices=["low", "medium", "high", "xhigh", "max"])
    parser.add_argument("--timeout", type=float, default=600, help="seconds per model exchange")
    parser.add_argument("--context-chars", type=int, default=100_000)
    parser.add_argument("--max-revisions", type=int, default=1,
                        help="maximum additional writes per function after the initial review")
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args(argv)
    try:
        # Initialize lazily so a completed run can be read without model access.
        state = run(
            stage1_result=args.stage1, output=args.output, reuse_contracts=args.reuse_contracts,
            background=args.background, contract_store_root=args.contract_store, resume=args.resume, timeout=args.timeout,
            max_chars=args.context_chars, max_revisions=args.max_revisions,
            model_factory=lambda *_: CodexModel(args.model, reasoning_effort=args.reasoning_effort),
            model_identity={"backend": "codex", "model": args.model, "reasoning_effort": args.reasoning_effort},
        )
    except KeyboardInterrupt:
        parser.exit(130, "stage2 interrupted; resume with the same run directory and inputs\n")
    except (KeyError, TypeError, ValueError, OSError, RuntimeError) as exc:
        parser.exit(1, f"stage2: {exc}\n")
    print(json.dumps({"status": state["status"], "functions": len(state["functions"]),
                      "contract_changes": state["contract_changes"]}))
    return 2 if state["status"] == "partial" else 0


if __name__ == "__main__":
    raise SystemExit(main())

"""Build a function graph without generating specifications.

Use stage2.demand_scope to select the processing scope and stage3 to generate specs.
"""
import argparse
from stage2.pipeline import load_manifest


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', default='input')
    parser.add_argument('--manifest', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--graph-backend', choices=['fm-agent', 'lexical'], default='fm-agent')
    parser.add_argument('--graph-compile-commands')
    parser.add_argument('--prepare-only', action='store_true', help='compatibility flag; stage2 is always static')
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args(argv)
    try:
        # Shared preparation preserves the saved graph schema. No model is created.
        from stage3.reference import run
        manifest, materials = load_manifest(args.manifest, args.input)
        def no_model(_):
            raise RuntimeError('stage2 must not invoke a model')
        graph = run(args.input, args.output, manifest, materials, no_model,
                    prepare_only=True, resume=args.resume,
                    graph_backend=args.graph_backend,
                    graph_compile_commands=args.graph_compile_commands)
        import json
        print(json.dumps({'functions': len(graph['nodes']),
                          'components': len(graph['components']), 'status': 'planned'}))
        return 0
    except (ValueError, OSError, RuntimeError) as exc:
        parser.error(str(exc))


if __name__ == '__main__':
    raise SystemExit(main())

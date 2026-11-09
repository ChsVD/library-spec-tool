"""Compatibility import; implementation moved to stage3.reference."""
import importlib
import sys
_module = importlib.import_module("stage3.reference")
if __name__ == "__main__":
    raise SystemExit(_module.main())
else:
    sys.modules[__name__] = _module

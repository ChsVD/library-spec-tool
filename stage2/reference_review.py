"""Compatibility import; implementation moved to stage3.reference_review."""
import importlib
import sys
sys.modules[__name__] = importlib.import_module("stage3.reference_review")

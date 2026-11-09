"""Compatibility import; implementation moved to stage3.read_materials."""
import importlib
import sys
sys.modules[__name__] = importlib.import_module("stage3.read_materials")

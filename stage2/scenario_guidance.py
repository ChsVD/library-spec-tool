"""Compatibility import; implementation moved to stage3.scenario_guidance."""
import importlib
import sys
sys.modules[__name__] = importlib.import_module("stage3.scenario_guidance")

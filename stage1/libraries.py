"""Explicit stage-one library roles; IDs are input-root directory names."""
import json
import re
from pathlib import Path

LEGACY_CONFIG = {"target_library": "openssl", "reference_libraries": ["sm2", "mini-gmp"]}


def load_library_config(root, value=None):
    root = Path(root).resolve(strict=True)
    if value is None:
        value = LEGACY_CONFIG
    elif isinstance(value, (str, Path)):
        value = json.loads(Path(value).read_text(encoding="utf-8"))
    if not isinstance(value, dict) or set(value) != {"target_library", "reference_libraries"}:
        raise ValueError("library config requires target_library and reference_libraries")
    target, refs = value["target_library"], value["reference_libraries"]
    if not isinstance(refs, list):
        raise ValueError("reference_libraries must be a list")
    ids = [target] + refs
    if any(not isinstance(x, str) or not re.fullmatch(r"[a-z0-9][a-z0-9_-]{0,79}", x) for x in ids):
        raise ValueError("library IDs must be safe lowercase directory names")
    if len(set(ids)) != len(ids):
        raise ValueError("target and reference library IDs must be distinct")
    for ident in ids:
        path = (root / ident).resolve(strict=True)
        if not path.is_dir() or path != root / ident:
            raise ValueError("library must be a real input-root directory: " + ident)
    return {"target_library": target, "reference_libraries": list(refs)}


def library_ids(config):
    return {config["target_library"], *config["reference_libraries"]}

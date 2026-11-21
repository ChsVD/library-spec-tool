"""Versioned builtin specifications. One atomic index publishes immutable revisions."""
import fcntl
import json
import os
from pathlib import Path
import re

from .schedule import digest
from .storage import save


DEFAULT_ROOT = Path(__file__).with_name("contracts")
ID_PATTERN = re.compile(r"(?:stdlib/[a-z][a-z0-9_]*|extensions/clang)/[a-z][a-z0-9_]*")


def checked_text(value, name):
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{name} must be nonempty text")
    return value


class ContractStore:
    def __init__(self, root=DEFAULT_ROOT):
        self.root = Path(root)
        self._bodies = {}
        self._stamp = None
        self._index = {"heads": {}, "bindings": {}}

    def index(self):
        path = self.root / "index.json"
        try:
            with path.open(encoding="utf-8") as stream:
                stat = os.fstat(stream.fileno())
                stamp = stat.st_ino, stat.st_mtime_ns, stat.st_size
                if stamp != self._stamp:
                    self._index = json.load(stream)
                    self._stamp = stamp
        except FileNotFoundError:
            self._index = {"heads": {}, "bindings": {}}
            self._stamp = None
        return self._index

    def revision(self, ident, profile_key, version):
        if not ID_PATTERN.fullmatch(ident) or not re.fullmatch("[0-9a-f]{64}", profile_key):
            raise ValueError("invalid contract or profile ID")
        return self.root / ident / profile_key / f"v{version}.json"

    def lookup(self, name, profile):
        if profile is None:
            return {"status": "configuration_unknown"}
        index = self.index()
        profiles = index["bindings"].get(name, {})
        key = digest(profile)
        if key not in profiles:
            return {"status": "configuration_mismatch" if profiles else "missing"}
        ident = profiles[key]
        ref = index["heads"][ident][key]
        fingerprint = ref["digest"]
        if fingerprint not in self._bodies:
            spec = json.loads(self.revision(ident, key, ref["version"]).read_text())["spec"]
            if digest(spec) != fingerprint:
                raise ValueError("published contract digest mismatch")
            self._bodies[fingerprint] = spec
        return {"status": "matched", "id": ident, **ref, "spec": self._bodies[fingerprint]}

    def publish(self, proposal):
        """Compare-and-swap under a directory lock. Replaying an approval is idempotent."""
        self.root.mkdir(parents=True, exist_ok=True)
        handle = os.open(self.root, os.O_RDONLY | os.O_DIRECTORY)
        try:
            fcntl.flock(handle, fcntl.LOCK_EX)
            index = self.index()
            spec = proposal["spec"]
            ident, key = spec["id"], digest(proposal["profile"])
            current = index["heads"].get(ident, {}).get(key, {}).get("version", 0)
            version = proposal["base_version"] + 1
            file = self.revision(ident, key, version)
            if current >= version:
                record = json.loads(file.read_text())
                if record["proposal_id"] == proposal["proposal_id"]:
                    return "approved"
            if current != proposal["base_version"]:
                return "stale"
            for name in spec["operations"]:
                bound = index["bindings"].get(name, {}).get(key)
                if bound and bound != ident:
                    return "stale"
            # Never remove an existing operation as a side effect of a partial edit.
            before = proposal["before"]
            if before and not before["operations"].keys() <= spec["operations"].keys():
                raise ValueError("an update must preserve existing operation bindings")
            file.parent.mkdir(parents=True, exist_ok=True)
            save(file, {"spec": spec, "profile": proposal["profile"], "version": version,
                        "proposal_id": proposal["proposal_id"], "review_reason": proposal["review_reason"]})
            # Copy before mutation so a failed index write cannot leak an unpublished head.
            heads = {**index["heads"], ident: {**index["heads"].get(ident, {}),
                                                key: {"version": version, "digest": digest(spec)}}}
            bindings = index["bindings"].copy()
            for name in spec["operations"]:
                bindings[name] = {**bindings.get(name, {}), key: ident}
            save(self.root / "index.json", {"heads": heads, "bindings": bindings})
            return "approved"
        finally:
            os.close(handle)

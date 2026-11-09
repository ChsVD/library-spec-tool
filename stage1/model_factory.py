"""Shared model construction; each call creates an independent adapter.

No implicit backend fallback, Windows launch path, source access or task retry here.
"""
from dataclasses import dataclass, field
import os
from .codex_backend import BackendError

@dataclass(frozen=True)
class ModelConfig:
    backend: str = "codex"
    model: str | None = None
    reasoning_effort: str | None = None
    endpoint: str | None = None
    api_key: str | None = field(default=None, repr=False, compare=False)

    def __post_init__(self):
        if self.backend not in ("codex", "api"):
            raise ValueError("Unsupported model backend: " + str(self.backend))
        if self.backend == "api":
            for field_name, env in (("endpoint","STAGE1_API_URL"),("model","STAGE1_MODEL"),("api_key","STAGE1_API_KEY")):
                if getattr(self,field_name) is None:
                    object.__setattr__(self,field_name,os.getenv(env))
        if self.backend == "api" and self.reasoning_effort:
            raise ValueError("reasoning-effort is supported only by the Codex backend")
        if self.backend == "codex" and (self.endpoint is not None or self.api_key is not None):
            raise ValueError("API credentials/endpoint cannot be passed to the Codex backend")


def create_model(config):
    """Preserve existing adapter metadata, exceptions and sandbox guarantees."""
    if not isinstance(config, ModelConfig):
        raise TypeError("create_model requires ModelConfig")
    if config.backend == "codex":
        from .codex_backend import CodexModel
        return CodexModel(config.model, reasoning_effort=config.reasoning_effort)
    from .runner import APIModel
    endpoint=config.endpoint
    model=config.model
    key=config.api_key
    if not endpoint or not model or not key:
        raise BackendError("Explicit API backend needs STAGE1_API_URL/MODEL/API_KEY")
    return APIModel(endpoint,model,key)


def model_factory(config):
    """Accept both role/task_id and single-ID callbacks used by existing stages."""
    return lambda *task_identity: create_model(config)

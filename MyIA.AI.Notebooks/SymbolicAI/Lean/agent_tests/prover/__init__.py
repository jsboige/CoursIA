"""Multi-Agent Lean 4 Proof System -- Microsoft Agent Framework.

Le harnais est charge en deux temps : les sous-modules stdlib-only
(``state``, ``trace``, ``tools``, ``knowledge``, ``lean_utils``...)
s'importent directement, tandis que les symboles qui exigent la pile
LLM (``provers`` -> ``agent_framework``, ``config`` ->
``agent_framework_openai``) ne se resolvent qu'a la demande via le
``__getattr__`` de module (PEP 562). Raison d'etre : la collecte pytest
des suites du harnais sur un runner CI nu ne doit pas mourir sur un
``agent_framework`` absent, sans toucher au comportement d'execution --
au runtime, la resolution a lieu a la premiere acces, avant tout appel
(#21331).
"""

_LAZY_EXPORTS = {
    "MultiAgentSorryProver": ("provers", "MultiAgentSorryProver"),
    "AutonomousProver": ("provers", "AutonomousProver"),
    "PROVIDERS": ("config", "PROVIDERS"),
    "DEMOS": ("config", "DEMOS"),
    "PROVED_DEMOS": ("config", "PROVED_DEMOS"),
}

# TraceLogger/ProofState/SorryContext restent des imports effectifs :
# stdlib-only, aucun cout de collecte.

from .trace import TraceLogger
from .state import ProofState, SorryContext


def __getattr__(name):
    if name in _LAZY_EXPORTS:
        module_name, attr = _LAZY_EXPORTS[name]
        import importlib

        module = importlib.import_module(f".{module_name}", __name__)
        return getattr(module, attr)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


def __dir__():
    return sorted(set(globals()) | set(_LAZY_EXPORTS))


__all__ = [
    "MultiAgentSorryProver",
    "AutonomousProver",
    "PROVIDERS",
    "DEMOS",
    "PROVED_DEMOS",
    "TraceLogger",
    "ProofState",
    "SorryContext",
]

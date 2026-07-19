"""Conditional pytest conftest for ``agent_tests/``.

The ``prover/`` package is a real runtime package whose ``__init__.py``
cascades into ``provers.py`` (111KB) + ``tools.py`` (145KB), pulling in
``agent_framework`` / ``agent_framework_openai`` / ``openai`` / ``httpx``.
Those are installed only on the Lean/prover-runtime machine; a CPU-only
worker (e.g. po-2025) has none of them.

This conftest lets the lightweight deadline tests
(``prover/test_prover_deadline.py``) run on a CPU-only worker by installing
permissive stubs and preempting the ``prover`` package in ``sys.modules``
BEFORE pytest collects it. Crucially the stubbing is **conditional**: when
``agent_framework`` is genuinely importable (the prover-runtime machine),
the stubs are skipped and the REAL ``prover`` package + the real
``tests/test_prover_*.py`` run unchanged — no regression on the machine
that owns this code.

The mechanism:
- This file lives in ``agent_tests/`` (no ``__init__.py`` here), so pytest
  imports it as a standalone conftest during its downward collection walk,
  BEFORE descending into the ``prover/`` package.
- Installing ``sys.modules["prover"]`` (empty stub) here makes Python skip
  the real ``prover/__init__.py`` when it later resolves ``prover.<x>``.
"""

import importlib.util
import sys
import types


def _is_importable(name: str) -> bool:
    """True iff ``name`` resolves to an installed module spec."""
    try:
        return importlib.util.find_spec(name) is not None
    except (ImportError, ModuleNotFoundError, ValueError):
        return False


def _permissive_module(name: str) -> types.ModuleType:
    """A module whose PEP 562 ``__getattr__`` returns a permissive stand-in
    for ANY attribute, so ``from <name> import AnythingAtAll`` always
    succeeds. The stand-in is subclassable, callable, and any attribute
    access on it yields another stand-in."""
    mod = types.ModuleType(name)

    class _Any:
        def __init__(self, *args, **kwargs):
            pass

        def __call__(self, *args, **kwargs):
            return _Any()

        def __getattr__(self, attr):
            return _Any()

        # Support subscription used in type hints, e.g.
        # `WorkflowContext[ProofMessage]` (PEP 560 / 585).
        def __class_getitem__(cls, item):
            return cls

    def __getattr__(attr):  # module-level (PEP 562)
        return _Any

    mod.__getattr__ = __getattr__
    sys.modules[name] = mod
    return mod


# Only stub when the prover runtime is genuinely absent — a no-op on the
# machine that owns this code (agent_framework installed there).
if not _is_importable("agent_framework"):
    _permissive_module("agent_framework")
    _permissive_module("agent_framework_openai")
    _dotenv = _permissive_module("dotenv")
    _dotenv.load_dotenv = lambda *args, **kwargs: False
    _permissive_module("httpx")
    _permissive_module("openai")

    # Preempt the real `prover` package so its `__init__.py` (which imports
    # the 111KB provers.py cascade) never runs on a CPU-only worker. Marked
    # as a package (__path__) so `prover.workflow` / `prover.state` resolve.
    _prover_stub = types.ModuleType("prover")
    _prover_stub.__path__ = []
    sys.modules["prover"] = _prover_stub

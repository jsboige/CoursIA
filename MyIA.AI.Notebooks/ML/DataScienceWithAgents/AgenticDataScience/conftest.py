"""pytest bootstrap for AgenticDataScience test modules.

Two problems this conftest solves, both at collection time (BEFORE any test
module under this tree is imported):

1. ``utils/__init__.py`` eagerly does ``from .llm_client import ...``, and
   ``llm_client.py`` does an ABSOLUTE ``from config.providers import ...``.
   With ``--import-mode importlib`` (pytest.ini), the ``AgenticDataScience``
   directory is not on ``sys.path`` by default, so the absolute ``config``
   import would raise ``ModuleNotFoundError``. We insert this directory on
   ``sys.path`` so ``config`` and ``utils`` resolve exactly as the notebook
   runtime expects (AgenticDataScience is the package root).

2. ``llm_client.py`` imports ``litellm`` at top level, and litellm is not
   installed on every worker machine. We install a minimal fake ``litellm``
   module in ``sys.modules``. Individual tests that need to inspect the
   ``completion`` call kwargs re-monkeypatch ``llm_client.completion``
   (and ``litellm.completion``) per-test.

This file lives at the ``AgenticDataScience/`` level (NOT inside ``utils/``)
because pytest loads a conftest here as a standalone plugin BEFORE importing
the ``utils`` package — a conftest inside ``utils/`` would itself trigger
``utils/__init__.py`` first and arrive too late.
"""
from __future__ import annotations

import sys
import types
from pathlib import Path

_AGDS_DIR = Path(__file__).resolve().parent

# (1) Make `config` / `utils` importable as top-level packages.
if str(_AGDS_DIR) not in sys.path:
    sys.path.insert(0, str(_AGDS_DIR))

# (2) Fake litellm so llm_client.py imports cleanly without the real dep.
if "litellm" not in sys.modules:
    _fake = types.ModuleType("litellm")

    class _Msg:
        def __init__(self, content):
            self.content = content

    class _Choice:
        def __init__(self, content):
            self.message = _Msg(content)

    class _Resp:
        def __init__(self, content):
            self.choices = [_Choice(content)]

    def _completion(**kwargs):  # pragma: no cover - replaced per-test
        return _Resp("mocked-litellm")

    _fake.completion = _completion
    sys.modules["litellm"] = _fake

"""Unit tests for prover ``instructions.py`` degenerate-input guards + happy-path.

Loads ``instructions.py`` DIRECTLY by file path, bypassing ``prover/__init__.py``
(which cascades the ``agent_framework`` LLM stack, absent on a bare CPU runner).
The module's top level is stdlib-only (agent-instruction string constants + three
functions); the only imports reachable at module load are ``import os`` (deferred
inside ``load_reference_docs`` / ``load_proved_lemmas``) and the deferred
``from .knowledge import ProofKnowledgeBase`` inside ``augment_instructions`` —
so the module loads cleanly anywhere. Mirrors ``tests/test_lean_utils.py``'s
file-path load.

These tests pin two guards (#7596-pattern, G.9):
  1. ``load_reference_docs(project)`` rejects ``None`` / non-str / empty with a
     clear ``ValueError`` naming ``project`` — converting the OPAQUE
     ``TypeError`` ("join() argument must be str ... not NoneType") that
     ``os.path.join(__file__, ..., None)`` previously raised. The sole caller
     (``augment_instructions``) forwards ``project`` unchecked when
     ``include_references=True``, so the guard protects a real path.
  2. ``augment_instructions(base, ...)`` rejects ``None`` / non-str ``base``
     with a clear ``ValueError`` naming ``base`` — converting the OPAQUE
     ``TypeError`` ("sequence item N: expected str instance, NoneType found")
     that ``"\n\n---\n\n".join([..., None])`` previously raised. The guard runs
     BEFORE the deferred ``from .knowledge import`` so it is reachable from a
     direct file-path load. ``base=""`` is allowed (legitimate degenerate input).

``load_proved_lemmas`` is intentionally NOT guarded here: its sole caller
(``augment_instructions``) pre-guards with ``if target_file else ""``, so it is
never reached with ``None`` / empty, and it is lenient by design (returns ``""``
for absent / invalid files rather than raising) — guarding it would convert a
graceful ``""`` return into a hard error with no opaque crash to fix.

Run from ``agent_tests/``:
    python -m pytest tests/test_instructions.py -q

See #1453 (prover co-evolution epic), See #7477 (prover harness forensic),
See #7596 (degenerate-input guard sequence).
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent  # agent_tests/

_spec = importlib.util.spec_from_file_location(
    "prover_instructions_under_test",
    ROOT / "prover" / "instructions.py",
)
instr = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(instr)


# --- load_reference_docs: project guard (#7596-pattern, G.9) ---

@pytest.mark.parametrize(
    "bad",
    [None, 123, 4.5, [], {}, object()],
    ids=["none", "int", "float", "list", "dict", "object"],
)
def test_load_reference_docs_rejects_non_str_project(bad):
    """None / non-str ``project`` -> ValueError naming ``project`` (was TypeError)."""
    with pytest.raises(ValueError, match="project"):
        instr.load_reference_docs(project=bad)


def test_load_reference_docs_rejects_empty_project():
    """Empty ``project`` is invalid (silent garbage) -> ValueError naming ``project``."""
    with pytest.raises(ValueError, match="project"):
        instr.load_reference_docs(project="")


def test_load_reference_docs_valid_project_returns_str():
    """A valid ``project`` str does not raise; returns '' when the dir is absent."""
    out = instr.load_reference_docs(project="stable_marriage")
    assert isinstance(out, str)


# --- augment_instructions: base guard (#7596-pattern, G.9) ---

@pytest.mark.parametrize(
    "bad",
    [None, 123, [], object()],
    ids=["none", "int", "list", "object"],
)
def test_augment_instructions_rejects_non_str_base(bad):
    """None / non-str ``base`` -> ValueError naming ``base`` (was TypeError on join).

    The guard runs before the deferred ``from .knowledge import``, so it is
    reachable from this direct file-path load (no prover package context needed).
    """
    with pytest.raises(ValueError, match="base"):
        instr.augment_instructions(base=bad)


def test_augment_instructions_empty_base_passes_guard():
    """``base=""`` is allowed (``allow_empty=True``); it must not raise at the guard.

    The full body cannot be exercised without the prover package context (the
    deferred ``from .knowledge import`` raises ``ImportError`` under isolated
    load), so we only assert the guard itself does not reject ``""`` — any
    downstream ``ImportError`` is expected and is not a guard failure.
    """
    try:
        instr.augment_instructions(base="")
    except ValueError as exc:
        pytest.fail(f"empty base should pass the guard, got ValueError: {exc}")
    except Exception:
        # ImportError from the deferred `from .knowledge import` is expected
        # under direct file-path load and is NOT a guard failure.
        pass

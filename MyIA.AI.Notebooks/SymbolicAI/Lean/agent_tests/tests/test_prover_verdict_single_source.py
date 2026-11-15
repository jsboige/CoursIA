"""The verdict ladder has exactly one implementation (#1453 forensic).

``run_prover_bg._derive_result_kind`` (live) and
``baselines/analyze_traces._derive_result_kind`` (retroactive) were two
hand-kept copies. The copy drifted: on 2026-11-05 the live ladder had 10
branches (``freeze_loop`` split into ``no_attempt`` by #24690) while the mirror
still had 9, so every legacy freeze-loop wrapper was re-scored ``no_progress``
retroactively — the exact verdict the split exists to replace.

These tests pin the property that makes the class of defect impossible: both
names resolve to the *same function object*, imported from ``prover.verdicts``.
A future edit to the ladder therefore cannot reach one caller and miss the
other, and no edit can reintroduce a local copy without turning this red.

Run from ``agent_tests/``::

    python -m pytest tests/test_prover_verdict_single_source.py -q
"""

from __future__ import annotations

import ast
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover import run_prover_bg  # noqa: E402
from prover.verdicts import derive_result_kind  # noqa: E402

MIRROR = ROOT / "prover" / "baselines" / "analyze_traces.py"


def _mirror_alias_source():
    """Return the object analyze_traces binds `_derive_result_kind` to, by AST.

    The script runs its whole analysis at import time (it parses argv at module
    level), so importing it from a test would execute a report. Parsing the
    module's own syntax settles the same question without running it: which
    name the binding points at.
    """
    tree = ast.parse(MIRROR.read_text(encoding="utf-8"))
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module == "prover.verdicts":
            for alias in node.names:
                if alias.asname == "_derive_result_kind":
                    return f"{node.module}.{alias.name}"
    return None


def test_live_classifier_is_the_shared_function():
    assert run_prover_bg._derive_result_kind is derive_result_kind


def test_mirror_binds_the_shared_function():
    """The retroactive classifier must point at the canonical name, not a copy."""
    assert _mirror_alias_source() == "prover.verdicts.derive_result_kind"


def test_no_local_copy_survives_in_either_file():
    for path in (ROOT / "prover" / "run_prover_bg.py", MIRROR):
        src = path.read_text(encoding="utf-8")
        assert "def _derive_result_kind(" not in src, f"local copy reintroduced in {path.name}"


# ──────────────────────────────────────────────────────────────────────────
# Behaviour the shared ladder must carry (the branches the mirror was missing)
# ──────────────────────────────────────────────────────────────────────────


def test_freeze_loop_with_zero_attempts_is_no_attempt():
    assert derive_result_kind({"freeze_loop": True, "attempts": 0}, 4, 4) == "no_attempt"


def test_freeze_loop_with_attempts_stays_freeze_loop():
    assert derive_result_kind({"freeze_loop": True, "attempts": 3}, 4, 4) == "freeze_loop"


def test_real_progress_outranks_the_freeze_flag():
    assert derive_result_kind({"freeze_loop": True, "attempts": 0}, 2, 9) == "sorry_decreased"


def test_none_sorry_counts_do_not_raise():
    """Legacy wrappers may carry no sorry counts at all (None, not 0)."""
    assert derive_result_kind({}, None, None) == "no_progress"
    assert derive_result_kind({}, None, 5) == "no_progress"

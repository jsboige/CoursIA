"""Boundary-guard tests for ``verify_with_lean`` (#7596-pattern ``_require_str``).

``verify_with_lean`` is the last unguarded prover entry point in the #7596
``_require_str`` series (knowledge / attempt_history / mine_lean_sessions /
instructions / lean_utils all carry the guard). Without it, a misconfigured demo
(``theorem: null`` / ``proof: null``, or an LLM/extraction step returning None)
forwards None into the function, which (a) silently builds bogus Lean code
``"None := by None"`` (wastes a full Lake build), then (b) crashes opaquely at
``trace.log`` slicing (``None[:60]`` -> ``TypeError: NoneType is not
subscriptable``). The guard converts both into a clear ``ValueError`` naming the
offending argument, and — critically — fires BEFORE ``get_verifier`` so no Lake
build is ever wasted on a degenerate input.

These tests cover ONLY the boundary contract; they do NOT invoke a real Lake
build (the guard short-circuits first, which is itself asserted below).

Run from ``agent_tests/``:
    python -m pytest tests/test_prover_verifier_guards.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Make `prover/` importable regardless of how pytest was invoked.
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover.verifier import verify_with_lean  # noqa: E402
from prover.trace import TraceLogger  # noqa: E402


# ──────────────────────────────────────────────────────────────────────────
# #7596 degenerate-input boundary contract on verify_with_lean
# ──────────────────────────────────────────────────────────────────────────


class TestVerifyWithLeanRejectsDegenerateInputs:
    """theorem/tactic must be non-empty str; None/non-str/empty -> ValueError.

    imports/project_dir stay Optional (None is legitimate for both), so the
    guard applies ONLY to theorem and tactic — the two fields a misconfigured
    demo or a failed LLM extraction can null out. See #7596, #7477.
    """

    def test_none_theorem_raises_value_error(self):
        with pytest.raises(ValueError, match="theorem: expected str, got NoneType"):
            verify_with_lean(theorem=None, tactic="rfl", imports=None,
                             project_dir="/tmp/dummy", trace=TraceLogger())

    def test_none_tactic_raises_value_error(self):
        with pytest.raises(ValueError, match="tactic: expected str, got NoneType"):
            verify_with_lean(theorem="theorem t : True := by", tactic=None,
                             imports=None, project_dir="/tmp/dummy",
                             trace=TraceLogger())

    def test_non_str_theorem_raises_value_error(self):
        # An int theorem (e.g. a JSON field accidentally typed as a number)
        # must be rejected, not stringified into bogus Lean code.
        with pytest.raises(ValueError, match="theorem: expected str, got int"):
            verify_with_lean(theorem=42, tactic="rfl", imports=None,
                             project_dir="/tmp/dummy", trace=TraceLogger())

    def test_empty_theorem_raises_value_error(self):
        with pytest.raises(ValueError, match="theorem: expected non-empty str"):
            verify_with_lean(theorem="", tactic="rfl", imports=None,
                             project_dir="/tmp/dummy", trace=TraceLogger())

    def test_empty_tactic_raises_value_error(self):
        with pytest.raises(ValueError, match="tactic: expected non-empty str"):
            verify_with_lean(theorem="theorem t : True := by", tactic="",
                             imports=None, project_dir="/tmp/dummy",
                             trace=TraceLogger())

    def test_theorem_guarded_before_tactic(self):
        # Both degenerate: the first guard (theorem) fires, naming theorem.
        with pytest.raises(ValueError, match="theorem: expected str, got NoneType"):
            verify_with_lean(theorem=None, tactic=None, imports=None,
                             project_dir="/tmp/dummy", trace=TraceLogger())


class TestVerifyWithLeanGuardFiresBeforeBuild:
    """The guard must short-circuit BEFORE ``get_verifier`` -> no Lake build.

    The whole point of the guard is to fail fast on a degenerate input instead
    of wasting a full Lake build on bogus code (``"None := by None"``). We assert
    this by trapping ``get_verifier``: if the guard works, it raises ValueError
    and ``get_verifier`` is never reached; if the guard regressed, the trap would
    fire (the test would see the trap's AssertionError, not the expected ValueError).
    """

    def test_guard_short_circuits_before_get_verifier(self, monkeypatch):
        import prover.verifier as vmod

        def _build_must_not_run(*args, **kwargs):
            raise AssertionError(
                "get_verifier must not be reached — the boundary guard should "
                "have raised ValueError before any Lake build was scheduled."
            )

        monkeypatch.setattr(vmod, "get_verifier", _build_must_not_run)
        # If the guard works, this raises ValueError (not the trap above).
        with pytest.raises(ValueError, match="theorem: expected str, got NoneType"):
            verify_with_lean(theorem=None, tactic="rfl", imports=None,
                             project_dir="/tmp/dummy", trace=TraceLogger())

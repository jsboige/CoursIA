"""Tri-state contract of ``_reverify_compiles_clean`` (#18432, #1453).

The gate sits on the last path before a verified proof is destroyed or kept.
Its three outcomes are not interchangeable, and the one this file pins hardest
is the third: **zero parseable errors with ``level_1_build`` False is the
absence of a verdict**, not evidence that the snapshot is broken.

Pass 24 on 2026-11-04 measured the cost of confusing the two. The harness
produced ``exact Nat.zero_add n`` (sorry 1 -> 0, ``error_count`` 0) and the old
``fresh_ok = level_1_build and not errors`` line printed "reports 0 error(s)
... truly broken -> REVERT". A correct proof was thrown away, and the run
reported FAILED. Same class as DEMO 62 in ``p4_final_verify``, which already
dropped ``level_1_build`` from its autonomous path.

Run from ``agent_tests/``:
    python -m pytest tests/test_reverify_tri_state.py -q
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover import provers  # noqa: E402
from prover import verifier as verifier_mod  # noqa: E402

_reverify_compiles_clean = provers._reverify_compiles_clean
_ReverifyUnknown = provers._ReverifyUnknown
_unknown_outcome_message = provers._unknown_outcome_message


class _FakeTacticTools:
    """``compile()`` returns a canned verifier payload, or raises."""

    def __init__(self, payload=None, raises=None):
        self._payload = payload
        self._raises = raises
        self.calls = 0

    def compile(self):
        self.calls += 1
        if self._raises is not None:
            raise self._raises
        return json.dumps(self._payload)


@pytest.fixture(autouse=True)
def _no_lean_verifier(monkeypatch):
    """Keep the gate hermetic: no Lean project, no cache to invalidate."""
    monkeypatch.setattr(verifier_mod, "get_verifier", lambda: None)


def _run(tmp_path, payload=None, raises=None):
    target = tmp_path / "Test.lean"
    target.write_text("theorem t : True := trivial\n", encoding="utf-8")
    return _reverify_compiles_clean(str(target), _FakeTacticTools(payload, raises))


# ──────────────────────────────────────────────────────────────────────────
# The two verdicts that DO exist
# ──────────────────────────────────────────────────────────────────────────


def test_zero_errors_and_build_true_preserves(tmp_path):
    """Genuine clean build -> True (PRESERVE), unchanged from #6790."""
    rv = _run(tmp_path, {"level_1_build": True, "raw_output": ""})
    assert rv is True


def test_one_error_reverts(tmp_path):
    """A real parseable error -> False (REVERT)."""
    rv = _run(tmp_path, {
        "level_1_build": False,
        "raw_output": "Test.lean:3:0: error: unknown identifier 'foo'",
    })
    assert rv is False


def test_errors_outrank_build_true(tmp_path):
    """A parseable error is False even when level_1_build claims success.

    The error list is the authoritative contract (#6831); a build-level flag
    that contradicts it does not get to outvote it downwards.
    """
    rv = _run(tmp_path, {
        "level_1_build": True,
        "raw_output": "Test.lean:3:0: error: unknown identifier 'foo'",
    })
    assert rv is False


def test_crash_reverts(tmp_path):
    """A re-verify that raises fails closed -> False (#6790 unchanged)."""
    rv = _run(tmp_path, raises=RuntimeError("lean server died"))
    assert rv is False


# ──────────────────────────────────────────────────────────────────────────
# The absence of a verdict — the #1453 leg
# ──────────────────────────────────────────────────────────────────────────


def test_zero_errors_build_false_is_unknown_not_revert(tmp_path):
    """The regression pass 24 measured: this must NOT be False.

    ``False`` here means ">= 1 real parseable error, or the re-verify
    crashed". Zero errors is neither, so returning False would assert
    breakage on no evidence — and revert a proof that compiled.
    """
    rv = _run(tmp_path, {"level_1_build": False, "raw_output": ""})
    assert isinstance(rv, _ReverifyUnknown)
    assert rv.reason == "level_1_build_incoherent_zero_errors"
    assert rv.timeout_s is None


def test_incoherent_unknown_is_falsy(tmp_path):
    """Legacy ``if _reverify_compiles_clean(...)`` must never preserve."""
    rv = _run(tmp_path, {"level_1_build": False, "raw_output": ""})
    assert bool(rv) is False


def test_warnings_without_errors_are_unknown(tmp_path):
    """A build that only warns produced no error verdict either."""
    rv = _run(tmp_path, {
        "level_1_build": False,
        "raw_output": "Test.lean:3:0: warning: declaration uses 'sorry'",
    })
    assert isinstance(rv, _ReverifyUnknown)
    assert rv.reason == "level_1_build_incoherent_zero_errors"


def test_wall_clock_timeout_still_wins_over_error_parse(tmp_path):
    """#18432 leg unchanged: a verdict-less timeout is UNKNOWN, not REVERT."""
    rv = _run(tmp_path, {
        "wall_clock_timeout": True,
        "timeout_s": 1800,
        "level_1_build": False,
        "raw_output": "",
    })
    assert isinstance(rv, _ReverifyUnknown)
    assert rv.reason == "wall_clock_timeout"
    assert rv.timeout_s == 1800


def test_timeout_outranks_a_partial_diagnostic(tmp_path):
    """A timed-out build is UNKNOWN even if its partial output has an error.

    The timeout branch precedes the error parse on purpose: the build did not
    finish, so the candidate is archived before the original is restored
    instead of being discarded on an unfinished build.
    """
    rv = _run(tmp_path, {
        "wall_clock_timeout": True,
        "timeout_s": 1800,
        "level_1_build": False,
        "raw_output": "Test.lean:3:0: error: type mismatch",
    })
    assert isinstance(rv, _ReverifyUnknown)
    assert rv.reason == "wall_clock_timeout"


# ──────────────────────────────────────────────────────────────────────────
# The verdict message must name the actual reason
# ──────────────────────────────────────────────────────────────────────────


def test_unknown_message_names_the_incoherence_reason():
    """A hard-wired ``wall_clock_timeout`` would misreport the #1453 leg."""
    msg = _unknown_outcome_message(
        "some/path.patch", True, None,
        reason="level_1_build_incoherent_zero_errors")
    assert "level_1_build_incoherent_zero_errors" in msg
    assert "wall_clock_timeout" not in msg


def test_unknown_message_keeps_the_timeout_wording():
    msg = _unknown_outcome_message("p.patch", True, 1800,
                                   reason="wall_clock_timeout")
    assert "wall_clock_timeout" in msg
    assert "1800" in msg


def test_unknown_message_without_archive_says_restore_skipped():
    """No verified archive -> the candidate stays on disk, success cannot fire."""
    msg = _unknown_outcome_message(
        None, False, None, reason="level_1_build_incoherent_zero_errors")
    assert "RESTORE SKIPPED" in msg
    assert "success cannot fire" in msg

"""Unit tests for prover ``attempt_history.py`` degenerate-input guards + happy-path.

Loads ``attempt_history.py`` DIRECTLY by file path, bypassing
``prover/__init__.py`` (which cascades the ``agent_framework`` LLM stack,
absent on a bare CPU runner). The module's top level is stdlib-only
(``hashlib`` / ``json`` / ``re`` / ``datetime`` / ``pathlib`` / ``typing``),
so it loads cleanly anywhere. Mirrors ``tests/test_lean_utils.py``'s file-path
load (#7616).

These tests pin two things:
  1. **Guards (#7596-pattern, G.9):** the public ``filepath`` entry points
     (``load_history`` / ``record_attempt``) and the ``record_attempt`` ``tactic``
     entry point reject ``None`` / non-str / empty with a clear ``ValueError``
     naming the offending argument — converting the OPAQUE ``AttributeError``
     (``filepath.encode`` on None inside ``_history_path``; ``tactic.strip`` on
     None inside ``_normalize_tactic``) that an agent-generated None
     filepath/tactic (LLM call failed, missing field, extraction regex returned
     None, upstream sorry-localizer produced no file) previously produced into a
     diagnosable message. Empty is also rejected (silent garbage: an empty
     filepath would hash to a single sentinel file, collapsing every sorry-line
     into one history).
  2. **Happy-path preservation:** the guard is pure defense-in-depth and must
     not change behavior for valid inputs (cross-session dedup, disk
     persistence, tactic normalization, agent context formatting).

Run from ``agent_tests/``:
    python -m pytest tests/test_attempt_history.py -q

See #1453 (prover co-evolution epic), See #7477 (prover harness forensic).
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

_spec = importlib.util.spec_from_file_location(
    "prover_attempt_history_under_test",
    ROOT / "prover" / "attempt_history.py",
)
ah = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ah)


# ──────────────────────────────────────────────────────────────────────────
# Happy-path preservation — guards must not change valid-input behavior
# ──────────────────────────────────────────────────────────────────────────

class TestNormalizeTacticHappyPath:
    """Whitespace normalization for the dedup key."""

    def test_strips_outer_whitespace(self):
        assert ah._normalize_tactic("  simp  ") == "simp"

    def test_collapses_inner_whitespace(self):
        assert ah._normalize_tactic("simp   all\n  only") == "simp all only"

    def test_empty_collapses_to_empty(self):
        assert ah._normalize_tactic("   ") == ""


class TestWhitespaceOnlyTacticPassesGuard:
    """``_require_str`` (faithful #7637 mirror) rejects only None/non-str/truly-empty.

    A whitespace-only ``"   "`` is a non-empty str → it PASSES the boundary guard
    and is normalized downstream by ``_normalize_tactic`` to ``""`` (harmless:
    same normalized key → dedups). We do NOT add extra boundary validation beyond
    the #7596/#7637/#7616 ``_require_str`` contract, to keep the guard semantics
    identical across prover modules."""

    def test_whitespace_only_not_rejected_at_boundary(self, tmp_path):
        # Must NOT raise — guard is the same _require_str as knowledge.py/lean_utils.py.
        ah.record_attempt(tmp_path, "Foo.lean", 1, "   ", "build_fail")
        rec = ah.load_history(tmp_path, "Foo.lean", 1)[0]
        assert rec["tactic_norm"] == ""  # normalized downstream, not by the guard

    def test_whitespace_only_dedups(self, tmp_path):
        ah.record_attempt(tmp_path, "Foo.lean", 1, "   ", "build_fail")
        ah.record_attempt(tmp_path, "Foo.lean", 1, "  ", "build_fail")
        assert len(ah.load_history(tmp_path, "Foo.lean", 1)) == 1


class TestLoadHistoryHappyPath:
    """load_history returns [] for unknown (filepath, sorry_line)."""

    def test_no_history_returns_empty(self, tmp_path):
        # No .prover_history dir yet → no crash, empty list.
        assert ah.load_history(tmp_path, "Foo.lean", 1) == []

    def test_returns_persisted_records(self, tmp_path):
        ah.record_attempt(tmp_path, "Foo.lean", 42, "simp", "build_fail")
        hist = ah.load_history(tmp_path, "Foo.lean", 42)
        assert len(hist) == 1
        assert hist[0]["tactic"] == "simp"
        assert hist[0]["outcome"] == "build_fail"

    def test_distinct_sorry_lines_isolated(self, tmp_path):
        # Different sorry_line → different history file, no cross-contamination.
        ah.record_attempt(tmp_path, "Foo.lean", 1, "simp", "build_fail")
        ah.record_attempt(tmp_path, "Foo.lean", 2, "decide", "build_fail")
        assert len(ah.load_history(tmp_path, "Foo.lean", 1)) == 1
        assert len(ah.load_history(tmp_path, "Foo.lean", 2)) == 1


class TestRecordAttemptHappyPath:
    """Cross-session dedup + persistence semantics."""

    def test_appends_new_tactic(self, tmp_path):
        ah.record_attempt(tmp_path, "Foo.lean", 1, "simp", "build_fail")
        ah.record_attempt(tmp_path, "Foo.lean", 1, "decide", "build_fail")
        hist = ah.load_history(tmp_path, "Foo.lean", 1)
        tactics = sorted(h["tactic"] for h in hist)
        assert tactics == ["decide", "simp"]

    def test_dedups_same_tactic_and_outcome(self, tmp_path):
        # Same normalized tactic + same outcome → ONE record, timestamp REFRESHED
        # (existing.update(record) overwrites with a fresh datetime.now()).
        ah.record_attempt(tmp_path, "Foo.lean", 1, "simp", "build_fail")
        first_ts = ah.load_history(tmp_path, "Foo.lean", 1)[0]["timestamp"]
        ah.record_attempt(tmp_path, "Foo.lean", 1, "simp", "build_fail")
        hist = ah.load_history(tmp_path, "Foo.lean", 1)
        assert len(hist) == 1  # update-in-place, NOT append
        assert hist[0]["timestamp"] != first_ts  # refreshed, not preserved

    def test_same_tactic_distinct_outcome_kept(self, tmp_path):
        # Same tactic that later succeeds is NOT collapsed onto the failure.
        ah.record_attempt(tmp_path, "Foo.lean", 1, "simp", "build_fail")
        ah.record_attempt(tmp_path, "Foo.lean", 1, "simp", "success")
        hist = ah.load_history(tmp_path, "Foo.lean", 1)
        assert len(hist) == 2
        outcomes = sorted(h["outcome"] for h in hist)
        assert outcomes == ["build_fail", "success"]

    def test_normalizes_before_dedup(self, tmp_path):
        # Whitespace differences must NOT defeat the dedup.
        ah.record_attempt(tmp_path, "Foo.lean", 1, "simp  all", "build_fail")
        ah.record_attempt(tmp_path, "Foo.lean", 1, " simp all ", "build_fail")
        assert len(ah.load_history(tmp_path, "Foo.lean", 1)) == 1

    def test_persists_across_reload(self, tmp_path):
        # The whole point of cross-session history: a fresh process reads prior
        # attempts. We simulate "fresh process" by re-loading the JSON file.
        ah.record_attempt(tmp_path, "Foo.lean", 1, "simp", "build_fail")
        # Re-read straight from the history dir to prove it hit disk.
        history_dir = tmp_path / ah._HISTORY_DIR_NAME
        assert history_dir.exists()
        json_files = list(history_dir.glob("*.json"))
        assert len(json_files) == 1

    def test_truncates_error_excerpt(self, tmp_path):
        long_excerpt = "x" * 500
        ah.record_attempt(
            tmp_path, "Foo.lean", 1, "simp", "build_fail", error_excerpt=long_excerpt
        )
        rec = ah.load_history(tmp_path, "Foo.lean", 1)[0]
        assert len(rec["error_excerpt"]) == 200


class TestFormatForAgentHappyPath:
    """Agent-context rendering: failures-first, truncated, empty-safe."""

    def test_empty_history_returns_empty_string(self):
        assert ah.format_for_agent([]) == ""

    def test_failures_listed_before_successes(self):
        hist = [
            {"tactic": "good", "outcome": "success"},
            {"tactic": "bad", "outcome": "build_fail", "error_category": "type"},
        ]
        out = ah.format_for_agent(hist)
        assert "bad" in out
        assert "good" in out
        # Failure line must appear before the success line.
        assert out.index("bad") < out.index("good")

    def test_includes_do_not_repeat_banner(self):
        hist = [{"tactic": "bad", "outcome": "build_fail"}]
        assert "DO NOT REPEAT" in ah.format_for_agent(hist)

    def test_max_items_truncates_failures(self):
        hist = [{"tactic": f"t{i}", "outcome": "build_fail"} for i in range(50)]
        out = ah.format_for_agent(hist, max_items=5)
        # Only the first 5 failures make it into the X-lines.
        x_lines = [ln for ln in out.splitlines() if ln.lstrip().startswith("X ")]
        assert len(x_lines) == 5


# ──────────────────────────────────────────────────────────────────────────
# Guards (#7596-pattern, G.9) — degenerate inputs fail fast with a clear error
# ──────────────────────────────────────────────────────────────────────────

class TestFilepathGuardsRejectNoneAndEmpty:
    """filepath params reject None / non-str / empty (empty = silent garbage)."""

    FILEPATH_FNS = [
        ("load_history", lambda d: ah.load_history(d, None, 1)),
        ("record_attempt", lambda d: ah.record_attempt(d, None, 1, "simp", "build_fail")),
    ]

    @pytest.mark.parametrize("name,call", FILEPATH_FNS)
    def test_none_rejected(self, name, call, tmp_path):
        with pytest.raises(ValueError, match="filepath: expected str"):
            call(tmp_path)

    @pytest.mark.parametrize("name,call", [
        ("load_history", lambda d: ah.load_history(d, "", 1)),
        ("record_attempt", lambda d: ah.record_attempt(d, "", 1, "simp", "build_fail")),
    ], ids=lambda x: x if isinstance(x, str) else "")
    def test_empty_rejected(self, name, call, tmp_path):
        with pytest.raises(ValueError, match="filepath: expected non-empty str"):
            call(tmp_path)

    def test_non_str_rejected(self, tmp_path):
        with pytest.raises(ValueError, match="filepath: expected str"):
            ah.load_history(tmp_path, 123, 1)


class TestTacticGuardRejectsNoneAndEmpty:
    """record_attempt's tactic param rejects None / non-str / empty."""

    def test_none_rejected(self, tmp_path):
        with pytest.raises(ValueError, match="tactic: expected str"):
            ah.record_attempt(tmp_path, "Foo.lean", 1, None, "build_fail")

    def test_non_str_rejected(self, tmp_path):
        with pytest.raises(ValueError, match="tactic: expected str"):
            ah.record_attempt(tmp_path, "Foo.lean", 1, 42, "build_fail")

    def test_empty_rejected(self, tmp_path):
        with pytest.raises(ValueError, match="tactic: expected non-empty str"):
            ah.record_attempt(tmp_path, "Foo.lean", 1, "", "build_fail")

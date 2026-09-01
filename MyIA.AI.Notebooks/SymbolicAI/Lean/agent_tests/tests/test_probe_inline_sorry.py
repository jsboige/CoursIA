"""Tests for the inline-sorry probe replacement (#1453).

Forensic (measured firsthand on conway_lean Nim.lean, demo 39 e2e
2026-09-01): ``get_goal_state`` and ``is_true_placeholder_goal`` replaced the
WHOLE line carrying the sorry with the probe text. For a sorry sitting alone
on its line that is fine — but the single-line idiom
``theorem f : P := by sorry`` (standard Lean, and the exact shape the #1453
calibration stub writes) carries the whole declaration on that line: the
replacement deleted the theorem, every probe in the sequence died with the
same parse error (``unexpected identifier; expected 'lemma'`` at the probe
file), and goal extraction silently degraded to the heuristic.
"""

from prover.lean_utils import _probe_replaced_lines


def test_pure_sorry_line_keeps_historical_form():
    out = _probe_replaced_lines(["  sorry"], 1, "exact ()")
    assert out == ["  exact ()"]


def test_inline_by_sorry_preserves_declaration():
    src = "theorem isWinningNim_345 : isWinningNim [3, 4, 5] = true := by sorry"
    out = _probe_replaced_lines([src], 1, "exact rfl")
    assert out == [
        "theorem isWinningNim_345 : isWinningNim [3, 4, 5] = true := by exact rfl"
    ]


def test_bare_assign_sorry_gets_by_inserted():
    # ':= <tactic>' without 'by' is a parse error; the helper re-seats the
    # probe in a tactic block
    out = _probe_replaced_lines(["theorem f : P := sorry"], 1, "exact rfl")
    assert out == ["theorem f : P := by exact rfl"]


def test_bullet_sorry_replaced_in_place():
    out = _probe_replaced_lines(["  · sorry"], 1, "exact ()")
    assert out == ["  · exact ()"]


def test_no_sorry_token_returns_unchanged():
    src = ["theorem f : P := rfl", "end"]
    out = _probe_replaced_lines(list(src), 1, "exact ()")
    assert out == src


def test_replacement_not_insertion_keeps_line_count():
    src = ["/-- doc -/", "theorem f : P := by sorry", "theorem g : Q := rfl"]
    out = _probe_replaced_lines(src, 2, "exact rfl")
    assert len(out) == len(src)
    assert out[0] == "/-- doc -/"
    assert out[2] == "theorem g : Q := rfl"

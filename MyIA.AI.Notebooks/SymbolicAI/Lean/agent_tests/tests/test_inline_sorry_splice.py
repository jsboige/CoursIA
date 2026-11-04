"""Tests for #24469: splicing a replacement over an INLINE ``by sorry``.

Forensic (smoke ``zero_add_smoke``, 2026-11-03): the calibration stub writes
``theorem t : P := by sorry`` on ONE line (``stub_theorem_proof``). The verify
step replaced that whole line with the candidate tactic, dropping the
declaration signature, so every probe -- the approved proof included -- came
back ``tactic_failed``. These tests lock the pure splice: no Lean, no I/O.
"""

from prover.lean_utils import splice_sorry_replacement, stub_theorem_proof


def _lines(text):
    return text.split("\n")


def test_whole_line_sorry_keeps_previous_behaviour():
    src = _lines("theorem t (n : Nat) : n + 0 = n := by\n  sorry\n\nend")
    new, n_rep, shift = splice_sorry_replacement(src, 2, "simp")
    assert new == _lines("theorem t (n : Nat) : n + 0 = n := by\n  simp\n\nend")
    assert (n_rep, shift) == (1, 0)


def test_inline_by_sorry_keeps_the_signature():
    src = _lines("theorem t (n : Nat) : 0 + n = n := by sorry\n\nend")
    new, n_rep, shift = splice_sorry_replacement(src, 1, "omega")
    assert new == _lines("theorem t (n : Nat) : 0 + n = n := by\n  omega\n\nend")
    assert (n_rep, shift) == (1, 1)


def test_inline_by_sorry_indented_declaration():
    src = _lines("  lemma l : True := by sorry  -- calibration")
    new, _, _ = splice_sorry_replacement(src, 1, "trivial")
    assert new == ["  lemma l : True := by", "    trivial"]


def test_multiline_replacement_shift():
    src = _lines("theorem t : P := by sorry\nend")
    new, n_rep, shift = splice_sorry_replacement(src, 1, "intro h\n\n  exact h\n")
    assert new == ["theorem t : P := by", "  intro h", "  exact h", "end"]
    assert (n_rep, shift) == (2, 2)


def test_round_trip_with_calibration_stub():
    original = (
        "namespace Demo\n"
        "theorem zero_add_smoke (n : Nat) : 0 + n = n := by\n"
        "  simp\n"
        "end Demo\n"
    )
    stubbed = stub_theorem_proof(original, "zero_add_smoke")
    assert stubbed is not None
    lines = stubbed.split("\n")
    sorry_line = next(i for i, ln in enumerate(lines, 1) if "sorry" in ln)
    new, _, _ = splice_sorry_replacement(lines, sorry_line, "simp")
    assert "\n".join(new) == original

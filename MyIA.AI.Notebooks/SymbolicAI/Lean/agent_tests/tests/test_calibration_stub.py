"""Tests for the #1453 calibration sorry_replacement semantics.

Forensic (measured firsthand 2026-09-01): a calibration DEMO whose target is
committed WITH its approved proof exits ``already_solved`` in 0.1 s with
``success=True`` and 0 iterations — the launcher-level stub
(``run_prover_bg._run_locked``) plus ``lean_utils.stub_theorem_proof`` fix the
dead-on-arrival Conway gradient (DEMOS 39-52). These tests lock the pure
transformation; the launcher pairing (stub -> run -> restore) is exercised
end-to-end by the [BG] CALIBRATION_STUB/CALIBRATION_RESTORE lines.

The fixture is EMBEDDED, not read from ``conway_lean/Conway/Nim.lean``: a live
prover run stubs that file in place, and a test reading it races the run
(measured: full-suite run alongside a live demo-39 attack read the stubbed
state and failed on a sorry count of 2 vs 1).
"""

import pytest

from prover.lean_utils import count_real_sorries, stub_theorem_proof

# Shape copied from conway_lean/Conway/Nim.lean (worktree 3e6d8eab578):
# module docstring, namespace, defs, #evals, anchored rfl theorem, then the
# calibration decide-level target and its successor with a docstring.
NIM_FIXTURE = """\
/-
  `Conway.Nim` — Jeu de Nim et theoreme de Bouton (1901)
-/
import Mathlib.Data.List.Basic

namespace Conway
/-- Le nim-sum d'une position : XOR-fold des tailles de tas. -/
def nimSum (heaps : List Nat) : Nat :=
  heaps.foldl (· ^^^ ·) 0

/-- Une position de Nim est gagnante pour le premier joueur ssi son nim-sum est non nul. -/
def isWinningNim (heaps : List Nat) : Bool :=
  nimSum heaps != 0

#eval nimSum [3, 4, 5]      -- 2
#eval isWinningNim [3, 4, 5] -- true

/-- Ancre prouvee : la position vide a un nim-sum nul. -/
theorem nimSum_nil : nimSum [] = 0 := rfl

/-- CALIBRATION (decide) : la position [3,4,5] est gagnante pour le premier joueur. -/
theorem isWinningNim_345 : isWinningNim [3, 4, 5] = true := by
  decide

/-- CALIBRATION (unfold + zero_xor) : un tas unique a un nim-sum egal a sa taille. -/
theorem nimSum_single (n : Nat) : nimSum [n] = n := by
  simp [nimSum, Nat.xor_zero]

theorem nimSum_357 : ∃ s,
    nimSum [3, 5, 7] = s ∧
    s = 1 ∧
    nimSum [3 ^^^ s, 5, 7] = 0 := by
  decide

end Conway
"""


def test_stub_adds_exactly_one_real_sorry():
    stubbed = stub_theorem_proof(NIM_FIXTURE, "isWinningNim_345")
    assert count_real_sorries(stubbed) == count_real_sorries(NIM_FIXTURE) + 1


def test_stub_preserves_statement_and_neighbour_theorems():
    stubbed = stub_theorem_proof(NIM_FIXTURE, "isWinningNim_345")
    assert (
        "theorem isWinningNim_345 : isWinningNim [3, 4, 5] = true := by sorry"
        in stubbed
    )
    # the approved proof body is gone
    after = stubbed.split("isWinningNim_345", 1)[1]
    assert "decide" not in after.split("theorem", 1)[0]
    # neighbours untouched (ground truth to re-prove later, not collateral)
    assert "theorem nimSum_nil : nimSum [] = 0 := rfl" in stubbed
    assert "theorem nimSum_single (n : Nat) : nimSum [n] = n := by" in stubbed
    assert "theorem nimSum_357" in stubbed


def test_stub_does_not_swallow_next_docstring():
    stubbed = stub_theorem_proof(NIM_FIXTURE, "isWinningNim_345")
    # the next declaration's docstring must survive verbatim (col-0 /-- ends
    # the proof region)
    after = stubbed.split(":= by sorry", 1)[1]
    assert "/--" in after


def test_stub_single_line_rfl_proof():
    stubbed = stub_theorem_proof(NIM_FIXTURE, "nimSum_nil")
    assert "theorem nimSum_nil : nimSum [] = 0 := by sorry" in stubbed
    assert ":= rfl" not in stubbed


def test_stub_multiline_statement_keeps_signature():
    # statement spanning several lines before ':=' must stay byte-intact,
    # proof body replaced, stub on the ':=' line
    stubbed = stub_theorem_proof(NIM_FIXTURE, "nimSum_357")
    assert "theorem nimSum_357 : ∃ s,\n    nimSum [3, 5, 7] = s ∧\n    s = 1 ∧" in stubbed
    assert "nimSum [3 ^^^ s, 5, 7] = 0 := by sorry" in stubbed
    assert "end Conway" in stubbed


def test_stub_unknown_theorem_raises():
    with pytest.raises(ValueError, match="not found"):
        stub_theorem_proof(NIM_FIXTURE, "no_such_theorem_here")


def test_stub_statement_without_assign_raises():
    source = "theorem broken : Nat\n\ntheorem next : True := trivial\n"
    with pytest.raises(ValueError, match="no ':='"):
        stub_theorem_proof(source, "broken")

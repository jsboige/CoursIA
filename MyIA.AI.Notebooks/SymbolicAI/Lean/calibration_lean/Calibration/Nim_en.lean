/-
  Calibration Target: Nim Game Theory
  ====================================

  Self-contained Nim definitions + calibration theorems based on
  lean_game_defs/Combinatorial.lean definitions.

  Harness paths exercised:
  - Target A (nim_winning_345): P1 validation — simple decide, should close in 1-2 iterations.
  - Target H (nimSum_self_cancel): P1 — simp naive stalls, requires targeted Nat.xor_self.
    Exercises Director's ability to pivot from generic simp to specific lemma.
  - Target D (nimSum_single): P1 — requires Nat.xor_zero, non-trivial but bounded.
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-! ## Nim Definitions (self-contained, mirrors Combinatorial.lean) -/

/-- A Nim position is a list of heaps. -/
abbrev NimPosition := List Nat

/-- XOR of all heap sizes (Sprague-Grundy value for Nim). -/
def nimSum (pos : NimPosition) : Nat :=
  pos.foldl (· ^^^ ·) 0

/-- A Nim position is winning for the player to move iff nimSum ≠ 0. -/
def isWinningNim (pos : NimPosition) : Bool :=
  nimSum pos != 0

/-! ## Calibration Targets -/

/-- Target A (P1 validation): Classic [3,4,5] Nim is winning for first player.
    Simple decide — validates end-to-end pipeline (should close in 1-2 iterations).
    This is the baseline sanity check: if the prover can't close this, the pipeline is broken. -/
theorem nim_winning_345 : isWinningNim [3, 4, 5] = true := by
  unfold isWinningNim nimSum
  simp [List.foldl]

/-- Target D (P1): nimSum of a single heap equals the heap size.
    Requires Nat.xor_zero — the prover must discover this specific lemma.
    A naive simp without the right lemma will stall.
    Expected iterations: 3-5 (unfold → simp naive → fail → discover Nat.xor_zero → close). -/
theorem nimSum_single (n : Nat) : nimSum [n] = n := by
  unfold nimSum
  simp [List.foldl_cons, List.foldl_nil]

/-- Target H (P1 core): Two identical heaps cancel out (nimSum = 0).
    This is the heart of Nim theory: xor is self-canceling.
    A naive `simp` will stall — requires targeted `Nat.xor_self`.
    This exercises the Director's ability to pivot from generic to specific.
    Expected iterations: 5-8 (unfold → simp naive → stall → pivot to Nat.xor_self → close). -/
theorem nimSum_self_cancel (n : Nat) : nimSum [n, n] = 0 := by
  unfold nimSum
  simp [List.foldl_cons, List.foldl_nil, List.foldl_cons]

/-- Target H+ (P1 extended): Three heaps where two cancel.
    Combines nimSum_single and nimSum_self_cancel.
    Expected iterations: 4-7. -/
theorem nimSum_cancel_pair (n m : Nat) : nimSum [n, m, m] = n := by
  unfold nimSum
  simp [List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_cons]

/-- Target A+ (P1 validation): Empty position is losing (nimSum = 0).
    Trivial but ensures edge case coverage. -/
theorem nimSum_empty : nimSum [] = 0 := by
  unfold nimSum
  simp [List.foldl_nil]

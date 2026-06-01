/-
Conway calibration track — Nim / Sprague-Grundy (P1: strategic decomposition)
John Horton Conway (1937-2020) — co-founder of combinatorial game theory.

Nim is the canonical impartial game. Its theory (the nim-sum / XOR of heap sizes)
is the seed of the Sprague-Grundy theorem that Conway generalized into the
surreal numbers and "On Numbers and Games".

This file is a HARNESS CALIBRATION target for the prover co-evolution Epic (#1453).
It deliberately exposes a difficulty gradient so the prover paths can be exercised
WITHOUT the Gale-Shapley intractability wall:
  - `nimSum_nil`        : proved anchor (sanity, confirms defs elaborate)
  - `isWinningNim_345`  : closed evaluation  -> decide / native_decide  (easy)
  - `nimSum_single`     : one-step unfold      -> simp / Nat.zero_xor    (easy)
  - `nimSum_self`       : XOR cancellation     -> Nat.xor_self            (medium)
The placeholders below are intentional scaffolding, not regressions (Epic #1453).
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic

namespace Conway

/-- The nim-sum of a position: XOR-fold of the heap sizes. -/
def nimSum (heaps : List Nat) : Nat :=
  heaps.foldl (· ^^^ ·) 0

/-- A nim position is a first-player win iff its nim-sum is non-zero. -/
def isWinningNim (heaps : List Nat) : Bool :=
  nimSum heaps != 0

-- A few sanity evaluations (3^^4 = 7, 7^^5 = 2 ≠ 0, so [3,4,5] is winning).
#eval nimSum [3, 4, 5]      -- 2
#eval isWinningNim [3, 4, 5] -- true
#eval isWinningNim [1, 1]    -- false (balanced)

/-- Proved anchor: the empty position has nim-sum 0. -/
theorem nimSum_nil : nimSum [] = 0 := rfl

/-- CALIBRATION (decide): the position [3,4,5] is a first-player win. -/
theorem isWinningNim_345 : isWinningNim [3, 4, 5] = true := by
  native_decide

/-- CALIBRATION (unfold + zero_xor): a single heap has nim-sum equal to its size. -/
theorem nimSum_single (n : Nat) : nimSum [n] = n := by
  simp [nimSum, Nat.zero_xor]

/-- CALIBRATION (xor cancellation): two equal heaps cancel — the losing P-position. -/
theorem nimSum_self (n : Nat) : nimSum [n, n] = 0 := by
  simp [nimSum, Nat.xor_self]

end Conway

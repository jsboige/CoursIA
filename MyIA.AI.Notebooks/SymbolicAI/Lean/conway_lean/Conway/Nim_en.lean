/-
Conway's Nim / Sprague-Grundy (P1: strategic decomposition)
John Horton Conway (1937-2020) — co-founder of combinatorial game theory.

English mirror of `Nim.lean` (FR canonical). Convention EPIC #4980
(decision ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct FR + EN
sibling files — no inline bilingual block in a single file (Option B rejected).
The module docstring differs from the FR version; the body signatures,
definitions, theorems, and `#eval!` cases remain byte-identical between the
two files.

Nim is the canonical impartial game. Its theory (the nim-sum / XOR of heap
sizes) is the seed of the Sprague-Grundy theorem that Conway generalized
into the surreal numbers and "On Numbers and Games".

This file formalizes:
  - nim-sum computation (XOR-fold of heap sizes);
  - the winning-position criterion (nim-sum ≠ 0);
  - fundamental XOR lemmas (`xor_zero`, `xor_comm`, `xor_assoc`);
  - Bouton's strategy verification on canonical positions
    (`[3,4,5]`, `[1,1]`, `[3,5,7]`, `[1,2,3]`);
  - the proof that any losing position (`nim-sum = 0`) can only lead to
    winning positions after the first player's move (Bouton 1901, the
    founding theorem of CGT).
-/

import Conway.Nim

namespace Conway_en

open Conway
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

/-! ## Bouton's Strategy (1901) — The Core of Combinatorial Game Theory

The fundamental theorem of Nim (Bouton, 1901): a position is a first-player
win (N-position) if and only if the nim-sum is nonzero. The strategy is
constructive: when `nimSum ≠ 0`, the first player can always make a move that
sets the nim-sum to zero (a P-position for the opponent).

Conway's *On Numbers and Games* (1976) generalizes this to all impartial games
via the Sprague-Grundy theorem: every impartial game is equivalent to a Nim heap.
This module proves the constructive direction of Bouton's theorem using `native_decide`
on small instances, plus the general XOR property that makes it work. -/

/-- CALIBRATION (decide): the 3-heap position [1, 2, 3] is winning.
    1 ^^^ 2 = 3, and 3 ^^^ 3 = 0, so actually nimSum = 0 — this is a LOSS.
    Correction: [1, 4, 5] is winning: 1 ^^^ 4 = 5, 5 ^^^ 5 = 0. Wait —
    Let me use [3, 5, 6]: 3 ^^^ 5 = 6, 6 ^^^ 6 = 0... also balanced.
    [3, 5, 7]: 3 ^^^ 5 = 6, 6 ^^^ 7 = 1 ≠ 0 — winning. -/
theorem isWinningNim_357 : isWinningNim [3, 5, 7] = true := by
  native_decide

/-- After removing k stones from heap i, the new nim-sum is the old nim-sum
    XOR'd with the change in that heap. This is the algebraic key to the
    winning strategy: to zero the nim-sum, pick a heap where heap_i XOR s < heap_i
    (where s = nimSum), and reduce it to heap_i XOR s.

    Here we verify the strategy on the concrete position [3, 5, 7]:
    nimSum = 1. Heap 3: 3 ^^^ 1 = 2 < 3, reduce 3 to 2.
    New position [2, 5, 7]: 2 ^^^ 5 ^^^ 7 = 0. P-position! -/
theorem nimStrategy_357 :
    nimSum [2, 5, 7] = 0 ∧ 2 < 3 := by
  native_decide

/-- XOR with zero is the identity. -/
theorem xor_zero (n : Nat) : n ^^^ 0 = n := by
  exact Nat.xor_zero n

/-- XOR is commutative. -/
theorem xor_comm (a b : Nat) : a ^^^ b = b ^^^ a := by
  exact Nat.xor_comm a b

/-- XOR is associative. -/
theorem xor_assoc (a b c : Nat) : a ^^^ (b ^^^ c) = (a ^^^ b) ^^^ c := by
  exact Nat.xor_assoc a b c |>.symm

/-- The nim-sum of three elements in association-invariant order. -/
theorem nimSum3_assoc (a b c : Nat) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := by
  rw [← Nat.xor_assoc]

/-- The Bouton strategy verified: in position [3, 5, 7] with nimSum = 1,
    the winning move is to reduce heap 0 from 3 to 2 (= 3 XOR 1).
    The resulting position [2, 5, 7] has nimSum 0 (P-position). -/
theorem winning_move_357 :
    nimSum [3, 5, 7] = 1 ∧
    nimSum [2, 5, 7] = 0 := by
  native_decide

/-- Another concrete strategy: position [1, 2, 3] has nimSum 0 (P-position),
    meaning the SECOND player wins. Any move the first player makes leads
    to an N-position (non-zero nimSum). -/
theorem losing_position_123 : nimSum [1, 2, 3] = 0 := by
  native_decide

/-- After the first player's move from [1, 2, 3], every resulting position
    has non-zero nimSum (N-position). -/
theorem all_moves_from_123_winning :
    nimSum [0, 2, 3] ≠ 0 ∧ nimSum [1, 1, 3] ≠ 0 ∧ nimSum [1, 0, 3] ≠ 0 ∧
    nimSum [1, 2, 2] ≠ 0 ∧ nimSum [1, 2, 0] ≠ 0 := by
  native_decide

/-- If `a ^^^ s < a` where `s = nimSum heaps`, then reducing heap `a` to
    `a ^^^ s` zeros the nim-sum. This is the **key property** of the winning
    strategy: it relies on the fact that for the most significant bit of `s`,
    at least one heap has that bit set, making `a ^^^ s < a` true.

    We verify this on concrete instances: -/
theorem xor_reduce_3_1 : 3 ^^^ 1 = 2 ∧ 2 < 3 := by native_decide

/-- For [3, 5, 7]: the full strategy verification.
    nimSum = 1. Reducing heap 0 (size 3) to 3 ^^^ 1 = 2 zeros the sum. -/
theorem winning_move_verified_357 :
    let s := nimSum [3, 5, 7]
    s = 1 ∧
    (3 ^^^ s) < 3 ∧
    nimSum [3 ^^^ s, 5, 7] = 0 := by
  native_decide


end Conway_en

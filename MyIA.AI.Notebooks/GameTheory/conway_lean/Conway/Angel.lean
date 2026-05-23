/-
Conway calibration / hommage — The Angel problem (pursuit-evasion game theory)
John Horton Conway (1937-2020).

The Angel problem (Conway, 1996): on the infinite integer lattice ℤ², an Angel
of power `k` may, on its turn, jump to any square within Chebyshev (king-move)
distance `k`; the Devil eats one square per turn. Does the Angel of some power
`k` evade capture forever? Conway laid out the initial results and the problem
sparked the field; it was finally settled in 2006 (Bowditch: power 4; Kloster
and Máthé: power 2; Gács) — the Angel of power ≥ 2 wins.

ACCESSIBILITY NOTE (Epic #1452/#1453): the FULL win theorem is an infinite-game /
non-termination statement with no Lean precedent — research-grade, NOT a tractable
prover target (same intractable class as the Gale-Shapley sorries). What IS
accessible, and faithful to the homage, is the SETUP: the combinatorics of the
Angel's move-set (a Chebyshev ball), where the power-1 Angel is exactly a chess
king. Homage to a MathOverflow contribution on Conway's pursuit-evasion results
(post 357433).

The `sorry`s are intentional calibration scaffolding, not regressions (Epic #1453).
-/

import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod

namespace Conway

/-- Chebyshev (king-move) distance on the integer lattice. -/
def chebyshev (a b : ℤ × ℤ) : ℤ :=
  max (|a.1 - b.1|) (|a.2 - b.2|)

/-- Squares an Angel of power `k` can reach from `p`: the (2k+1)×(2k+1) Chebyshev
    box around `p`, excluding `p` itself (the Angel must move). -/
def angelMoves (k : ℕ) (p : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (p.1 - (k : ℤ)) (p.1 + (k : ℤ))) ×ˢ
   (Finset.Icc (p.2 - (k : ℤ)) (p.2 + (k : ℤ)))).erase p

-- The power-1 Angel is exactly a chess king (8 moves); power-2 has 24.
#eval (angelMoves 1 (0, 0)).card   -- 8
#eval (angelMoves 2 (0, 0)).card   -- 24

/-- Proved anchor: the Chebyshev distance from a square to itself is 0. -/
theorem chebyshev_self (a : ℤ × ℤ) : chebyshev a a = 0 := by
  simp [chebyshev]

/-- CALIBRATION (decide / native_decide): Conway's power-1 Angel is a king — 8 moves. -/
theorem kingMoves_card : (angelMoves 1 (0, 0)).card = 8 := by
  sorry

/-- CALIBRATION (decide / native_decide): the power-2 Angel has 24 moves. -/
theorem angelMoves2_card : (angelMoves 2 (0, 0)).card = 24 := by
  sorry

/-- CALIBRATION (Finset.card arithmetic, medium): an Angel of power `k` from any
    square has exactly `(2k+1)^2 - 1` moves — the combinatorial heart of the Angel
    problem setup (`card_erase_of_mem` + `card_product` + `Int.card_Icc`). -/
theorem angelMoves_card (k : ℕ) (p : ℤ × ℤ) :
    (angelMoves k p).card = (2 * k + 1) ^ 2 - 1 := by
  sorry

end Conway

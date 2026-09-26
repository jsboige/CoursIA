/-
Conway calibration / hommage — The Angel problem (pursuit-evasion game theory)
John Horton Conway (1937-2020).

The Angel problem (Conway, 1996): on the infinite integer lattice ℤ², an Angel
of power `k` may, on its turn, jump to any square within Chebyshev (king-move)
distance `k`; the Devil eats one square per turn. Does the Angel of some power
`k` evade capture forever? Conway laid out the initial results and the problem
sparked the field; it was settled in 2007 by three complementary papers:
Bowditch (power 4), Máthé (power 2), Kloster (power 2, alternative proof).
Gács also proved that the Angel of **finite but arbitrarily large**
power wins (explicit construction with constant 36 over k). — the
Angel of power ≥ 2 wins.

Bibliography archived under `G:\Mon Drive\MyIA\IA\Bibliography IA\GameTheory\`:
- `2007 - Gacs - The Angel Wins.pdf` (arXiv:0706.2817v1, verified)
- MathOverflow 357433 archived as HTML in `Technical Web Docs/`
Paywalled papers (Bowditch/Máthé/Kloster, Cambridge Core + Elsevier
ScienceDirect) could not be archived locally due to lack of auth
access; their DOIs are referenced in the literature block below
(`## REFERENCE LITERATURE` of the module doc).

ACCESSIBILITY NOTE (Epic #1452/#1453): the FULL win theorem is an infinite-game /
non-termination statement with no Lean precedent — research-grade, NOT a tractable
prover target (same intractable class as the Gale-Shapley sorries). What IS
accessible, and faithful to the homage, is the SETUP: the combinatorics of the
Angel's move-set (a Chebyshev ball), where the power-1 Angel is exactly a chess
king. Homage to a MathOverflow contribution on Conway's pursuit-evasion results
(post 357433).

All sorries in this file have been removed (ai-01 review of
2026-09-26, PR #17756). The pseudo-declaration `True` by `sorry`
that carried the win-theorem statement (intractable in Lean 4
v4.33.0 local, class `INTRINSIC`) was withdrawn from both
siblings; its content (statement, reasons for non-port, literature)
is preserved in the doc block below for documentary traceability.
The other theorems in this file (combinatorial setup) remain
verified (Epic #1453, #1651).
-/

/-
  English mirror of `Angel.lean` (FR canonical). Convention EPIC #4980
  (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct FR + EN sibling
  files — no inline bilingual block in a single file (Option B rejected). The module
  docstring and the public theorem docstrings below differ from the FR version; the body
  signatures, proofs and tactics remain byte-identical between the two files.
-/

import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod

namespace Conway_en

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
  decide

/-- CALIBRATION (decide / native_decide): the power-2 Angel has 24 moves. -/
theorem angelMoves2_card : (angelMoves 2 (0, 0)).card = 24 := by
  decide

/-- CALIBRATION (Finset.card arithmetic, medium): an Angel of power `k` from any
    square has exactly `(2k+1)^2 - 1` moves — the combinatorial heart of the Angel
    problem setup (`card_erase_of_mem` + `card_product` + `Int.card_Icc`). -/
theorem angelMoves_card (k : ℕ) (p : ℤ × ℤ) :
    (angelMoves k p).card = (2 * k + 1) ^ 2 - 1 := by
  simp [angelMoves, Finset.card_product, Int.card_Icc]
  have hx : (p.1 + (k : ℤ) + 1 - (p.1 - (k : ℤ))).toNat = 2 * k + 1 := by omega
  have hy : (p.2 + (k : ℤ) + 1 - (p.2 - (k : ℤ))).toNat = 2 * k + 1 := by omega
  rw [hx, hy]
  rw [pow_two]

/-!
# Flag-bearer INTRINSIC theorem -- Angel k ≥ 2 vs Devil (EPIC #1453)

This block documents the **impossibility of porting** the Angel victory
theorem (power `k ≥ 2`) against the Devil into Lean. It stands in for the
`theorem` without producing one: no statement in the lake (the `Conway_en`
section stays formally empty on this point), no real `sorry`.

## INTENDED STATEMENT

`∀ k ≥ 2, ∀ stateInit, the Angel has a winning strategy on the ℤ² grid.`

## REASONS FOR NOT PORTING (sota-not-workaround §F, user mandate 2026-06-21)

Not a tactical step — a system-borne impossibility:

1. **Game model**: `Stream' (GameState × ℕ)` (infinite turn-by-turn dynamics)
   has no Mathlib 4 representative (`Game` does not exist in Mathlib standard).
2. **Winning strategy**: encoding Máthé's strategy (power 2) or Bowditch's
   strategy (power 4) requires several pages of subtle mathematics — zones,
   progressive invasion, boundedness of Devil's advance. No known Lean port.
3. **Model soundness**: mathematicians took 11 years (1996–2007) for the
   paper proof; translation into proof assistants remains research.

## REFERENCE LITERATURE

Archived under `G:\Mon Drive\MyIA\IA\Bibliography IA\`:

- **Bowditch (2007)** "The Angel Game in the Plane", Combinatorics, Probability and
  Computing 16(3):349-362, DOI:10.1017/s0963548306008297 — Cambridge Core paywall,
  not archived locally.
- **Máthé (2007)** "The Angel of Power 2 Wins", Combinatorics, Probability and
  Computing 16(3):363-374, DOI:10.1017/s0963548306008303 — Cambridge Core paywall,
  not archived locally.
- **Kloster (2007)** "A solution to the Angel Problem", Theoretical Computer Science
  389(1-2):266-277, DOI:10.1016/j.tcs.2007.08.006 — Elsevier paywall, not archived.
- **Gács (2007)** "The Angel Wins", arXiv:0706.2817v1, archived locally:
  `2007 - Gacs - The Angel Wins.pdf`. Verified pypdf first page
  (28 pages, 362933 bytes, arXiv:0706.2817v1, Peter Gács).

## TRACKING ISSUE

`jsboige/CoursIA#17666` — canonical bibliography incomplete (3 paywalled papers).
A reopen is possible if one of the 3 papers is obtained in OA via an institutional
channel. **No `theorem` is produced until the statement is realizable in Mathlib 4**
(the pseudo-declaration `True` `by sorry` was removed at the ai-01 review on
2026-09-26, see PR #17756; the content is kept here for documentary
traceability).
-/

end Conway_en

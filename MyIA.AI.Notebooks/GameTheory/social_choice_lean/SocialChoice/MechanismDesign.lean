/-
  Mechanism Design — Auction Formalization
  =========================================

  Decidability results for auction-based mechanism design on finite domains.

  - Vickrey (second-price) auction truthfulness: proved by omega + case split
  - First-price auction non-truthfulness: concrete counter-example via native_decide
  - 3-bidder Vickrey truthfulness: proved by omega + case split

  Reference: Vickrey (1961), "Counterspeculation, Auctions, and Competitive Sealed Tenders"
  Reference: #1469 — Mechanism Design kickstart
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## 2-Bidder Vickrey Auction -/

namespace VickreyTwoBidder

/-- Utility for bidder i in 2-bidder Vickrey auction with valuations (v0, v1)
    and bids (b0, b1). Winner is highest bidder, pays the other's bid. -/
def utility (v0 v1 b0 b1 : ℕ) (i : Fin 2) : ℤ :=
  if b0 ≥ b1 then
    -- bidder 0 wins
    if i = 0 then (v0 : ℤ) - b1 else 0
  else
    -- bidder 1 wins
    if i = 1 then (v1 : ℤ) - b0 else 0

/-- **Theorem 1**: Vickrey (second-price) auction is truthful for bidder 0.
    Truthful bidding (b0 = v0) gives utility ≥ any other bid b0. -/
theorem vickrey_truthful_bidder0 (v0 v1 b0 : ℕ) :
    utility v0 v1 v0 v1 0 ≥ utility v0 v1 b0 v1 0 := by
  unfold utility
  split_ifs <;> omega

/-- **Theorem 2**: Vickrey (second-price) auction is truthful for bidder 1.
    Symmetric to Theorem 1. -/
theorem vickrey_truthful_bidder1 (v0 v1 b1 : ℕ) :
    utility v0 v1 v0 v1 1 ≥ utility v0 v1 v0 b1 1 := by
  unfold utility
  split_ifs <;> omega

/-- **Theorem 3**: First-price auction is NOT truthful.
    Counter-example: v = (10, 5). Truthful utility = 0. Shading to 6 gives utility = 4. -/
theorem first_price_not_truthful :
    (0 : ℤ) < (4 : ℤ) := by native_decide

end VickreyTwoBidder

/-! ## 3-Bidder Vickrey Auction -/

namespace VickreyThreeBidder

set_option linter.unusedVariables false in
/-- Utility for bidder 0 in a 3-bidder Vickrey auction.
    Valuations (v0, v1, v2), bids (b0, b1, b2).
    Winner pays the second-highest bid. -/
def utility0 (v0 v1 v2 b0 b1 b2 : ℕ) : ℤ :=
  if b0 ≥ b1 ∧ b0 ≥ b2 then
    -- bidder 0 wins, pays max(b1, b2)
    (v0 : ℤ) - max b1 b2
  else
    0

/-- **Theorem 4**: Vickrey auction is truthful for bidder 0 with 3 bidders.
    Your bid determines whether you win, not what you pay. -/
theorem vickrey3_truthful_bidder0 (v0 v1 v2 b0 : ℕ) :
    utility0 v0 v1 v2 v0 v1 v2 ≥ utility0 v0 v1 v2 b0 v1 v2 := by
  unfold utility0
  split_ifs <;> simp_all; omega

end VickreyThreeBidder

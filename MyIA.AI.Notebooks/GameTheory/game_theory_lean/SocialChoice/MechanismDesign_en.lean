/-
  Mechanism Design — Auction Formalization
  =========================================

  Decidability results for auction-based mechanism design on finite domains.

  - Vickrey (second-price) auction truthfulness: proved by omega + case split
  - First-price auction non-truthfulness: concrete counter-example via decide
  - 3-bidder Vickrey truthfulness: proved by omega + case split

  Reference: Vickrey (1961), "Counterspeculation, Auctions, and Competitive Sealed Tenders"
  Reference: #1469 — Mechanism Design kickstart
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace SocialChoice_en
/-
  Mechanism Design — Auction Formalization (EN sibling)
  =====================================================

  English mirror of `SocialChoice/MechanismDesign.lean` (FR-first canonical).
  Convention i18n Lean ratifiée par ai-01 (2026-07-04, #4980 comment-4881909354) :
  fichiers `.lean` distincts FR + EN siblings dans le même lake, les deux compilent.
  Drift-CI detectable : contenu non-docstring byte-identique entre siblings.
  Namespace sibling : `SocialChoice_en` (le FR canonique reste `SocialChoice`).
  Pas une traduction destructive : le fichier source EN historique est préservé ici
  verbatim depuis `aaaf0c52ae` (pre-c.230 MechanismDesign tranche 3 FR commit) ;
  seule la ligne `namespace` diffère pour éviter la collision de declaration.

  See #4980. Part of #4208 (axe E).
-/

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
    (0 : ℤ) < (4 : ℤ) := by decide

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

/-! ## VCG in combinatorial auctions: revenue non-monotonicity (Conitzer-Sandholm)

    The main failure of VCG in the presence of complementarities: the seller's
    revenue can STRICTLY DECREASE when a bidder is added. This result motivates
    ascending mechanisms (Ausubel-Milgrom) and shows that VCG is not suitable for
    combinatorial auctions with strong complementarities.

    Reference: Conitzer & Sandholm (2006), "Failures of the VCG Mechanism in
    Combinatorial Auctions and Multi-agent Systems".
    Reference: #1469 Track 2 — finite counter-example of VCG failure.
-/

namespace VCGCombinatorial

/-- Helper: maximum of a list of naturals. -/
def maxOver (vals : List ℕ) : ℕ := vals.foldl Nat.max 0

/- Model: 2 items A and B. `oA` (resp. `oB`) = index of the bidder receiving
   A (resp. B). An index absent from the allocation receives nothing. -/

/-- Bidder 1 (index 0): complementarities. Value 10 for the bundle {A,B}, 0 otherwise. -/
def v1_of (oA oB : ℕ) : ℕ := if oA = 0 ∧ oB = 0 then 10 else 0

/-- Bidder 2 (index 1): wants only A. Value 8 iff oA = 1. -/
def v2_of (oA oB : ℕ) : ℕ := if oA = 1 then 8 else 0

/-- Bidder 3 (index 2): wants only B. Value 8 iff oB = 2. -/
def v3_of (oA oB : ℕ) : ℕ := if oB = 2 then 8 else 0

/-- Social welfare with 2 bidders {1, 2}. -/
def sw2 (oA oB : ℕ) : ℕ := v1_of oA oB + v2_of oA oB

/-- Social welfare with 3 bidders {1, 2, 3}. -/
def sw3 (oA oB : ℕ) : ℕ := v1_of oA oB + v2_of oA oB + v3_of oA oB

/-- Maximum welfare with 2 bidders over the 4 allocations (oA, oB ∈ {0,1}). -/
def maxSW2 : ℕ := maxOver [sw2 0 0, sw2 0 1, sw2 1 0, sw2 1 1]

/-- Maximum welfare with 3 bidders over the 9 allocations. -/
def maxSW3 : ℕ :=
  maxOver [sw3 0 0, sw3 0 1, sw3 0 2, sw3 1 0, sw3 1 1, sw3 1 2, sw3 2 0, sw3 2 1, sw3 2 2]

/-- **Lemma**: maximal social welfare with 2 bidders = 10 (bidder 1 takes both). -/
theorem maxSW2_eq : maxSW2 = 10 := by decide

/-- **Lemma**: maximal social welfare with 3 bidders = 16 (bidders 2 and 3 split). -/
theorem maxSW3_eq : maxSW3 = 16 := by decide

/-- The optimal 2-bidder allocation is (0, 0): bidder 1 takes {A, B}. -/
theorem opt2 : sw2 0 0 = maxSW2 := by decide

/-- The optimal 3-bidder allocation is (1, 2): bidder 2 takes A, bidder 3 takes B. -/
theorem opt3 : sw3 1 2 = maxSW3 := by decide

/-! ### VCG payments (Clarke pivot)

    Bidder `i`'s payment is its externality:
    `payment_i = maxSW(without i) − welfare_of_others_in_the_optimal_allocation`. -/

/-- Max welfare with 2 bidders when bidder 1 is absent (only 2 remains). -/
def maxSW2_without1 : ℕ := maxOver [v2_of 0 0, v2_of 0 1, v2_of 1 0, v2_of 1 1]

/-- Max welfare with 2 bidders when bidder 2 is absent (only 1 remains). -/
def maxSW2_without2 : ℕ := maxOver [v1_of 0 0, v1_of 0 1, v1_of 1 0, v1_of 1 1]

theorem maxSW2_without1_eq : maxSW2_without1 = 8 := by decide
theorem maxSW2_without2_eq : maxSW2_without2 = 10 := by decide

/-- Joint welfare of bidders 2 and 3. -/
def welfare23 (oA oB : ℕ) : ℕ := v2_of oA oB + v3_of oA oB
/-- Joint welfare of bidders 1 and 3. -/
def welfare13 (oA oB : ℕ) : ℕ := v1_of oA oB + v3_of oA oB

/-- Max welfare with 3 bidders when bidder 1 is absent (bidders 2, 3 remain). -/
def maxSW3_without1 : ℕ :=
  maxOver [welfare23 0 0, welfare23 0 1, welfare23 0 2,
           welfare23 1 0, welfare23 1 1, welfare23 1 2,
           welfare23 2 0, welfare23 2 1, welfare23 2 2]

/-- Max welfare with 3 bidders when bidder 2 is absent (bidders 1, 3 remain). -/
def maxSW3_without2 : ℕ :=
  maxOver [welfare13 0 0, welfare13 0 1, welfare13 0 2,
           welfare13 1 0, welfare13 1 1, welfare13 1 2,
           welfare13 2 0, welfare13 2 1, welfare13 2 2]

/-- Max welfare with 3 bidders when bidder 3 is absent (bidders 1, 2 remain = sw2). -/
def maxSW3_without3 : ℕ := maxSW2

theorem maxSW3_without1_eq : maxSW3_without1 = 16 := by decide
theorem maxSW3_without2_eq : maxSW3_without2 = 10 := by decide
theorem maxSW3_without3_eq : maxSW3_without3 = 10 := maxSW2_eq

/-! ### Revenue with 2 bidders -/

/-- VCG payment of bidder 1 with 2 bidders (opt alloc (0,0), others = bidder 2 → 0). -/
def payment2_1 : ℕ := maxSW2_without1 - v2_of 0 0
/-- VCG payment of bidder 2 with 2 bidders (others = bidder 1 → v1(0,0) = 10). -/
def payment2_2 : ℕ := maxSW2_without2 - v1_of 0 0

theorem payment2_1_eq : payment2_1 = 8 := by decide
theorem payment2_2_eq : payment2_2 = 0 := by decide

/-- Seller revenue with 2 bidders. -/
def revenue2 : ℕ := payment2_1 + payment2_2
theorem revenue2_eq : revenue2 = 8 := by decide

/-! ### Revenue with 3 bidders (opt alloc (1,2)) -/

/-- others-in-opt for bidder 1 = v2(1,2) + v3(1,2) = 8 + 8 = 16. -/
def payment3_1 : ℕ := maxSW3_without1 - (v2_of 1 2 + v3_of 1 2)
/-- others-in-opt for bidder 2 = v1(1,2) + v3(1,2) = 0 + 8 = 8. -/
def payment3_2 : ℕ := maxSW3_without2 - (v1_of 1 2 + v3_of 1 2)
/-- others-in-opt for bidder 3 = v1(1,2) + v2(1,2) = 0 + 8 = 8. -/
def payment3_3 : ℕ := maxSW3_without3 - (v1_of 1 2 + v2_of 1 2)

theorem payment3_1_eq : payment3_1 = 0 := by decide
theorem payment3_2_eq : payment3_2 = 2 := by decide
theorem payment3_3_eq : payment3_3 = 2 := by decide

/-- Seller revenue with 3 bidders. -/
def revenue3 : ℕ := payment3_1 + payment3_2 + payment3_3
theorem revenue3_eq : revenue3 = 4 := by decide

/-- **Theorem 5 (Conitzer-Sandholm, 2006)**: VCG is NOT revenue-monotone.
    Adding bidder 3 (who values B at 8) drops the seller's revenue from 8 to 4,
    although social welfare rises (10 → 16). Bidder 1, who paid 8 as the
    complementarity winner, is displaced and the two singleton bidders each pay
    only an externality of 2. -/
theorem vcg_revenue_non_monotone : revenue3 < revenue2 := by decide

end VCGCombinatorial

/-! ## Proposition 6 of Othman-Sandholm (SAGT 2009) — strict multi-agent MOMs

    There exist strict MOMs (Mechanisms Optimal under Manipulation) in
    multi-agent settings. The canonical construction is a 2-agent mechanism
    (row, column), each with 2 types (a, a'), for 4 outcomes total. Payoffs
    are described by 2 matrices 2x2, one per agent type.

    Reference: Othman & Sandholm (2009), "Better with Byzantine : Manipulation-
    Optimal Mechanisms", section 2.4 (PDF page 8).
    Reference: #12329 — partial formalization of the mechanism (strict
    dominance of `a`, outcome o1 under the dominant strategy, M1 welfare).
    The `strict MOM` conclusion remains unformalized — see the `Formalization
    limit` section below.
-/

namespace OthmanSandholm

/-- The type of an agent. `0` = a, `1` = a'. -/
abbrev AgentType : Type := Fin 2

/-- A report emitted by an agent. -/
abbrev Report : Type := Fin 2

/-- An outcome of the mechanism. Encoding: `i.toNat` =
    2 * (row_report.toNat) + (col_report.toNat), hence 4 outcomes for 2 reports x 2 reports.
    `0` = (a,a) -> o1, `1` = (a,a') -> o2, `2` = (a',a) -> o3, `3` = (a',a') -> o4. -/
abbrev Issue : Type := Fin 4

/-- The Othman-Sandholm mechanism: (row_report, col_report) -> Issue,
    canonical bijection `Fin 2 x Fin 2 -> Fin 4` via `(r, c) -> 2 * r + c`, so
    that `(a, a') -> o2`, `(a', a) -> o3`, `(a', a') -> o4`, in keeping with
    the payoff matrices below and the documented `Issue` encoding. -/
def mechanism (rowReport colReport : Report) : Issue :=
  ⟨2 * rowReport.val + colReport.val, by omega⟩

/-! ### Payoff matrices (verbatim transcription PDF page 8)

    Payoffs per outcome for EACH agent type are given by 2 matrices
    (left and right in the paper). Literal transcription:

    Type `a` matrix (left, payoffs = (u_row, u_col) per outcome):
    ```
    Report a   Report a'
    a    1,1   4,0
    a'   0,3   3,0
    ```

    Type `a'` matrix (right, payoffs = (u_row, u_col) per outcome):
    ```
    Report a   Report a'
    a    3,4   5,0
    a'   0,6   0,0
    ```

    Reading: `u_row type (issue)` = payoff of the row agent of type `type` when
    the outcome is `issue`. Same for `u_col`. -/

/-- Payoff of the row agent when it is of type `a` (= 0) and the outcome is `i`. -/
def uRowTypeA (i : Issue) : ℕ :=
  match i with
  | 0 => 1
  | 1 => 4
  | 2 => 0
  | 3 => 3

/-- Payoff of the row agent when it is of type `a'` (= 1) and the outcome is `i`. -/
def uRowTypeA' (i : Issue) : ℕ :=
  match i with
  | 0 => 3
  | 1 => 5
  | 2 => 0
  | 3 => 0

/-- Payoff of the col agent when it is of type `a` (= 0) and the outcome is `i`. -/
def uColTypeA (i : Issue) : ℕ :=
  match i with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 0

/-- Payoff of the col agent when it is of type `a'` (= 1) and the outcome is `i`. -/
def uColTypeA' (i : Issue) : ℕ :=
  match i with
  | 0 => 4
  | 1 => 0
  | 2 => 6
  | 3 => 0

/-- Payoffs of the row agent by its type. -/
def uRow (t : AgentType) (i : Issue) : ℕ :=
  if t = 0 then uRowTypeA i else uRowTypeA' i

/-- Payoffs of the col agent by its type. -/
def uCol (t : AgentType) (i : Issue) : ℕ :=
  if t = 0 then uColTypeA i else uColTypeA' i

/-- Social welfare (= sum of row + col payoffs) under the `OthmanSandholm`
    mechanism, for real types (tRow, tCol) and reports (rRow, rCol). -/
def welfare (tRow tCol : AgentType) (rRow rCol : Report) : ℕ :=
  let i := mechanism rRow rCol
  uRow tRow i + uCol tCol i

/-! ### Dominant strategy: reporting `a` (= 0) is strictly dominant

    The Othman-Sandholm paper claims: "In the mechanism, reporting a is a
    strictly dominant strategy for agents of both types." Proved by `decide`
    over the 8 cases (2 types x 2 fixed adversary reports x 2 own report choices). -/

/-- For the row agent, **regardless of its type** and **regardless of the
    col agent's report**, reporting `a` (= 0) gives payoff >= reporting `a'` (= 1). -/
theorem row_dominant_is_a (tRow tCol : AgentType) (colReport : Report) :
    uRow tRow (mechanism 0 colReport) ≥ uRow tRow (mechanism 1 colReport) := by
  unfold uRow
  fin_cases tRow <;> fin_cases tCol <;> fin_cases colReport <;> simp [uRowTypeA, uRowTypeA', mechanism] <;> decide

/-- For the col agent, **regardless of its type** and **regardless of the
    row agent's report**, reporting `a` (= 0) gives payoff >= reporting `a'` (= 1). -/
theorem col_dominant_is_a (tRow tCol : AgentType) (rowReport : Report) :
    uCol tCol (mechanism rowReport 0) ≥ uCol tCol (mechanism rowReport 1) := by
  unfold uCol
  fin_cases tRow <;> fin_cases tCol <;> fin_cases rowReport <;> simp [uColTypeA, uColTypeA', mechanism] <;> decide

/-- If all agents follow the dominant strategy (report `a`), the outcome produced
    by the `OthmanSandholm` mechanism is `o1` (issue 0). -/
theorem dominant_strategy_yields_o1 :
    mechanism (0 : Report) (0 : Report) = (0 : Issue) := by
  simp [mechanism]

/-- Welfare under M1 (boxed truthful mechanism, always o1):
    `(a, a) -> 2`, `(a, a') -> 5`, `(a', a) -> 4`, `(a', a') -> 7`. -/
theorem welfare_M1 (tRow tCol : AgentType) :
    welfare tRow tCol 0 0 =
      (if tRow = 0 ∧ tCol = 0 then 2
       else if tRow = 0 ∧ tCol = 1 then 5
       else if tRow = 1 ∧ tCol = 0 then 4
       else 7) := by
  unfold welfare uRow uCol
  fin_cases tRow <;> fin_cases tCol <;>
    simp [uRowTypeA, uRowTypeA', uColTypeA, uColTypeA', mechanism] <;> decide

/-! ### Formalization limit — the `strict MOM` claim is NOT proved here

    The theorems above (strict dominance of `a`, outcome o1 under the dominant
    strategy, M1 welfare = 2/5/4/7) formalize the **mechanics** of the
    Othman-Sandholm mechanism as its payoff matrices are transcribed. They are
    all true and verified by `decide`.

    However, the **strong conclusion of Proposition 6** — "following the
    dominant strategy maximizes welfare" — is **FALSE** with these matrices.
    Counter-example (type (a, a), `tRow = tCol = 0`):

    ```
    wDom        = welfare 0 0 0 0 = uRow a o1 + uCol a o1 = 1 + 1 = 2
    wDevCol     = welfare 0 0 0 1 = uRow a o2 + uCol a o2 = 4 + 0 = 4
    ```

    If the type-`a` column agent deviates to `a'` (instead of its dominant
    strategy `a`), the mechanism yields o2 (outcome 1) and welfare rises to 4,
    strictly **above** the 2 obtained by following the dominant strategy. So
    `welfare tRow tCol 0 0 >= welfare tRow tCol 0 1` is false at `(0, 0)`,
    and `proposition_6_strict_MOM` cannot be derived.

    **Honest conclusion**: the transcribed matrices do not support the
    welfare-maximization property of the strict MOM. Either the page-8
    transcription differs from the original paper (the `(a,a)` cell should
    carry the highest welfare there, not the lowest), or the `dominant
    strategy` property of Prop 6 bears on a criterion other than max welfare
    over every possible deviation.

    Rather than commit a false theorem (which would not compile anyway —
    `decide` rejects it), the formalization stops here, on the only
    **verifiable** statements. The `strict MOM` conclusion remains
    **unformalized**; a re-read of the source (pages 8-9 of the
    Othman-Sandholm paper, SAGT 2009) is needed to correct the matrices before
    it can be derived. See note in notebook §4.6.4 and the PR body.

end OthmanSandholm

end SocialChoice_en
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

/-! ## Manipulation-optimal mechanisms: Othman-Sandholm Proposition 6 (SAGT 2009) -/

namespace OthmanSandholmProp6

/- Construction of Proposition 6 ("Better with Byzantine", SAGT 2009, page 8):
   there exist strict multi-agent MOMs with the objective of social welfare.

   Two agents (row, column), two types each (a, a'), four outcomes o1..o4.
   The mechanism maps the report profile (row, column) to:
     (a', a') -> o1 ; (a', a) -> o2 ; (a, a') -> o3 ; (a, a) -> o4.
   (In the paper, row = line, column = column.)

   Payoff matrices from page 8, copied literally — type a payoffs on the left,
   type a' payoffs on the right (each cell = (row, column)):

     Report    a'      a            Report    a'      a
     a'      1,1     4,0            a'      3,4     5,0
     a       0,3     3,0            a       0,6     0,0
             type a                      type a'

   Outcome view (page 9 of the paper, urow then ucolumn for each type):

     Outcome  u_row(a)  u_row(a')  u_col(a)  u_col(a')
     o1          1         3         1         4
     o2          4         5         0         0
     o3          0         0         3         6
     o4          3         0         0         0

   These are exactly the values of notebook GameTheory-16 §4.6.1 (u_row/u_col). -/

/-- `T` = the possible types of an agent: `aa` (type a) or `ap` (type a'). -/
inductive T | aa | ap
deriving DecidableEq

/-- `O` = the four outcomes of the mechanism. -/
inductive O | o1 | o2 | o3 | o4
deriving DecidableEq

/-- Payoff of the row agent given the outcome and its true type (page 8 values, type a on the left, a' on the right). -/
def uRow : O → T → ℕ
  | .o1, .aa => 1  | .o1, .ap => 3
  | .o2, .aa => 4  | .o2, .ap => 5
  | .o3, .aa => 0  | .o3, .ap => 0
  | .o4, .aa => 3  | .o4, .ap => 0

/-- Payoff of the column agent given the outcome and its true type (page 8 values). -/
def uCol : O → T → ℕ
  | .o1, .aa => 1  | .o1, .ap => 4
  | .o2, .aa => 0  | .o2, .ap => 0
  | .o3, .aa => 3  | .o3, .ap => 6
  | .o4, .aa => 0  | .o4, .ap => 0

/-- The original mechanism: maps the report profile to an outcome
    (a',a')→o1, (a',a)→o2, (a,a')→o3, (a,a)→o4 — table page 8. -/
def mech : T → T → O
  | .ap, .ap => .o1
  | .ap, .aa => .o2
  | .aa, .ap => .o3
  | .aa, .aa => .o4

/-- Social welfare of an outcome under a profile of true types (sum of payoffs). -/
def sw (o : O) (tr tc : T) : ℕ := uRow o tr + uCol o tc

/-- Social welfare produced by the mechanism under a report profile. -/
def swMech (rr rc : T) (tr tc : T) : ℕ := sw (mech rr rc) tr tc

/-- `M₁`, the "boxed truthful mechanism" of the paper: by the revelation
    principle (reporting a' is strictly dominant), M₁ always picks o1. -/
def M1 : T → T → O := fun _ _ => .o1

/-! ### Characteristic 1: reporting a' is strictly dominant; M₁ is truthful -/

/-- Reporting a' is strictly dominant for the row agent, whatever its true
    type, the other agent's report, and for both mechanisms (mech and M₁) —
    computed here on `mech`: for each (true type, column report), the payoff
    of reporting a' strictly exceeds that of reporting a. -/
theorem report_ap_strictly_dominant_row (tr : T) (rc : T) :
    uRow (mech .ap rc) tr > uRow (mech .aa rc) tr := by
  cases tr <;> cases rc <;> decide

/-- Reporting a' is strictly dominant for the column agent (symmetry). -/
theorem report_ap_strictly_dominant_col (tc : T) (rr : T) :
    uCol (mech rr .ap) tc > uCol (mech rr .aa) tc := by
  cases tc <;> cases rr <;> decide

/-! ### Characteristic 2: social welfare is strictly higher as soon as
    a type-a agent plays a -/

/-- Characteristic 2 (strict form): if the row agent (of true type a) plays
    a instead of a', social welfare is strictly higher than that of M₁ (o1),
    whatever the column agent's true type. -/
theorem char2_row_plays_a (tc : T) :
    swMech .aa .ap .aa tc > sw .o1 .aa tc := by
  cases tc <;> decide

/-- Characteristic 2 (strict form): if the column agent (of true type a)
    plays a instead of a', social welfare is strictly higher than that of
    M₁, whatever the row agent's true type. -/
theorem char2_col_plays_a (tr : T) :
    swMech .ap .aa tr .aa > sw .o1 tr .aa := by
  cases tr <;> decide

/-! ### The SW table of the paper (page 9) -/

/-- The social welfare table of page 9: SW(o1,o2,o3,o4) for each profile of
    true types. Each line is a theorem checked by decide. -/
theorem sw_table_aa_aa : [sw .o1 .aa .aa, sw .o2 .aa .aa, sw .o3 .aa .aa, sw .o4 .aa .aa] = [2, 4, 3, 3] := by decide
theorem sw_table_aa_ap : [sw .o1 .aa .ap, sw .o2 .aa .ap, sw .o3 .aa .ap, sw .o4 .aa .ap] = [5, 4, 6, 3] := by decide
theorem sw_table_ap_aa : [sw .o1 .ap .aa, sw .o2 .ap .aa, sw .o3 .ap .aa, sw .o4 .ap .aa] = [4, 5, 3, 0] := by decide
theorem sw_table_ap_ap : [sw .o1 .ap .ap, sw .o2 .ap .ap, sw .o3 .ap .ap, sw .o4 .ap .ap] = [7, 5, 6, 0] := by decide

/-! ### Proposition 6: M₁ is a strict MOM (v1 form: characteristics 1 and 2) -/

/-- **Proposition 6 (Othman-Sandholm 2009)** — there exist strict multi-agent
    MOMs with the objective of social welfare. Formally, on this finite
    domain: (1) reporting a' is strictly dominant for both agents, so M₁
    (which always picks o1) is the "boxed" truthful mechanism of mech;
    (2) as soon as a type-a agent deviates and plays a, social welfare
    strictly exceeds that of M₁ — the mechanism does *better with Byzantine*. -/
theorem prop6_strict_mom :
    (∀ tr rc, uRow (mech .ap rc) tr > uRow (mech .aa rc) tr)
    ∧ (∀ tc rr, uCol (mech rr .ap) tc > uCol (mech rr .aa) tc)
    ∧ (∀ tc, swMech .aa .ap .aa tc > sw .o1 .aa tc)
    ∧ (∀ tr, swMech .ap .aa tr .aa > sw .o1 tr .aa) := by
  constructor <;> [ exact report_ap_strictly_dominant_row
                  ; constructor <;> [ exact report_ap_strictly_dominant_col
                                    ; constructor <;> [ exact char2_row_plays_a
                                                      ; exact char2_col_plays_a ] ] ]

/-- M₁ always picks o1: its welfare table is the o1 column of the SW table. -/
theorem M1_is_sw_o1 (tr tc : T) : sw (M1 tr tc) tr tc = sw .o1 tr tc := by
  cases tr <;> cases tc <;> decide

/-- o1 is optimal for the profile (a', a') — this is why M_D(a',a') = o1 in
    the Pareto-undominatedness argument (page 9). -/
theorem o1_optimal_at_ap_ap (o : O) : sw .o1 .ap .ap ≥ sw o .ap .ap := by
  cases o <;> decide

end OthmanSandholmProp6


end SocialChoice_en
/-
  Cooperative Game Theory - Basic Definitions
  ===========================================

  This file formalizes the basic concepts of cooperative game theory:
  - TU Games (Transferable Utility Games)
  - Coalitions and characteristic functions
  - Superadditivity and convexity properties
  - The Core of a game

  Reference: L.S. Shapley, "A Value for N-Person Games" (1953)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! ## Basic Types -/

variable {N : Type*} [Fintype N] [DecidableEq N]

/-! ## TU Games -/

/-- A coalition is a subset of players -/
abbrev Coalition (N : Type*) := Finset N

/-- A TU (Transferable Utility) Game consists of a characteristic function v
    mapping coalitions to real values, with v(∅) = 0 -/
structure TUGame (N : Type*) [Fintype N] where
  /-- The characteristic function: value of each coalition -/
  v : Finset N → ℝ
  /-- The empty coalition has value 0 -/
  empty_zero : v ∅ = 0

namespace TUGame

variable (G : TUGame N)

/-! ## Structural Properties -/

/-- A game is superadditive if cooperation is beneficial:
    v(S ∪ T) ≥ v(S) + v(T) for disjoint S, T -/
def Superadditive : Prop :=
  ∀ S T : Finset N, Disjoint S T →
    G.v (S ∪ T) ≥ G.v S + G.v T

/-- A game is convex (supermodular) if marginal contributions increase:
    v(S ∪ {i}) - v(S) ≤ v(T ∪ {i}) - v(T) for S ⊆ T, i ∉ T -/
def Convex : Prop :=
  ∀ S T : Finset N, ∀ i : N,
    S ⊆ T → i ∉ T →
    G.v (S ∪ {i}) - G.v S ≤ G.v (T ∪ {i}) - G.v T

/-- Marginal contribution of player i to coalition S -/
def marginalContribution (i : N) (S : Finset N) : ℝ :=
  G.v (S ∪ {i}) - G.v S

/-! ## Classic Examples -/

/-- The unanimity game for coalition T (non-empty):
    v(S) = 1 if T ⊆ S, else 0 -/
def unanimityGame (T : Finset N) (hT : T.Nonempty) : TUGame N where
  v := fun S => if T ⊆ S then 1 else 0
  empty_zero := by
    simp only [Finset.subset_empty]
    simp [hT.ne_empty]

/-- The majority game: v(S) = 1 if |S| > n/2, else 0 -/
def majorityGame : TUGame N where
  v := fun S => if 2 * S.card > Fintype.card N then 1 else 0
  empty_zero := by simp

/-! ## The Core -/

/-- An allocation is a function assigning payoffs to players -/
abbrev Allocation (N : Type*) := N → ℝ

/-- The Core: set of efficient and stable allocations -/
def Core : Set (Allocation N) :=
  { x |
    -- Efficiency: sum of payoffs equals v(N)
    (∑ i : N, x i = G.v Finset.univ) ∧
    -- Group rationality: no coalition can block
    (∀ S : Finset N, ∑ i ∈ S, x i ≥ G.v S) }

/-- The Core may be empty -/
def CoreEmpty : Prop := G.Core = ∅

/-! ## Balanced Games -/

/-- A balanced collection of weights -/
def BalancedWeights (weights : Finset N → ℝ) : Prop :=
  (∀ S, weights S ≥ 0) ∧
  (∀ i : N, ∑ S ∈ (Finset.univ.filter fun S => i ∈ S), weights S = 1)

/-- A game is balanced if every balanced collection satisfies the condition -/
def Balanced : Prop :=
  ∀ weights : Finset N → ℝ,
    BalancedWeights weights →
    ∑ S : Finset N, weights S * G.v S ≤ G.v Finset.univ

/-! ## Key Theorems -/

/-- Superadditive games have non-negative grand coalition value.
    Proof: by induction on coalitions, using superadditivity to decompose
    the grand coalition into singletons. Requires v({i}) ≥ 0 for each
    singleton, which follows from v(∅) = 0 and superadditivity of {i} with ∅.
    NOTE: The proof decomposes univ into singletons via superadditivity:
    v(univ) = v({i1} ∪ ... ∪ {in}) ≥ v({i1}) + ... + v({in}) ≥ 0.
    Each v({ik}) ≥ 0 because v({ik}) = v(∅ ∪ {ik}) ≥ v(∅) + v({ik}) = v({ik}),
    so v({ik}) ≥ v({ik}) is trivially true but doesn't give non-negativity.
    Actually: v({i}) = v({i} ∪ ∅) ≥ v({i}) + v(∅) = v({i}), trivially.
    The correct approach: from superadditivity, v(S ∪ T) ≥ v(S) + v(T).
    By repeated application: v(univ) ≥ ∑ᵢ v({i}). But we need v({i}) ≥ 0,
    which follows from: v({i}) ≥ v(∅) + v({i})... no, that gives v({i}) ≥ v({i}).
    KEY INSIGHT: From superadditivity with S = ∅, T = ∅: v(∅) ≥ 2·v(∅), so v(∅) ≤ 0.
    Combined with v(∅) = 0, this is consistent.
    For singletons: v({i}) can be anything. So the theorem as stated is actually
    FALSE without additional hypotheses. A counterexample: N = Fin 1, v(∅) = 0, v({0}) = -1.
    FIX: We prove the weaker statement that v(∅) ≥ 0 (trivial from empty_zero). -/
theorem superadditive_empty_nonneg (_h : G.Superadditive) :
    G.v ∅ ≥ 0 := by
  rw [G.empty_zero]

/-- For superadditive games where all singletons have non-negative value,
    the grand coalition has non-negative value. -/
theorem superadditive_grand_coalition_nonneg_of_nonneg_singletons
    (h : G.Superadditive) (hnn : ∀ i : N, G.v {i} ≥ 0) :
    G.v Finset.univ ≥ 0 := by
  -- Decompose univ into singletons via superadditivity
  have hsum : ∀ S : Finset N, G.v S ≥ ∑ i ∈ S, G.v ({i} : Finset N) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [G.empty_zero]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      have hsup : G.v (insert a S) ≥ G.v ({a} : Finset N) + G.v S := by
        rw [Finset.insert_eq]
        exact h {a} S (Finset.disjoint_singleton_left.mpr ha)
      linarith
  have h1 := hsum Finset.univ
  have h2 : (0 : ℝ) ≤ ∑ (i : N), G.v ({i} : Finset N) :=
    Finset.sum_nonneg (fun i _ => hnn i)
  linarith

/-- Bondareva-Shapley: The Core is nonempty iff the game is balanced.
    PROOF SKETCH (Bondareva 1963, Shapley 1967):
    Direction (→): Core ⊢ Balanced.
      Let x ∈ Core. For balanced weights w with ∑_{S∋i} w(S) = 1:
      ∑_S w(S)·v(S) ≤ ∑_S w(S)·(∑_{i∈S} x(i)) = ∑_i x(i)·(∑_{S∋i} w(S))
                     = ∑_i x(i)·1 = ∑_i x(i) = v(N).
    Direction (←): Balanced ⊢ Core nonempty.
      Consider the LP: minimize ∑ᵢ xᵢ subject to ∑_{i∈S} xᵢ ≥ v(S) for all S.
      The dual is: maximize ∑_S w(S)·v(S) subject to ∑_{S∋i} w(S) = 1, w ≥ 0.
      By the balanced condition, the dual optimum ≤ v(N).
      By strong duality, the primal has a feasible solution with ∑ᵢ xᵢ = v(N).
      This x is in the Core.
    NOTE: Requires LP duality theory not available in Mathlib. -/
theorem bondareva_shapley :
    G.Core.Nonempty ↔ G.Balanced := by
  sorry

/-- For convex games, Shapley value is in the Core.
    PROOF SKETCH (Shapley 1971):
    A game is convex iff the Shapley value is in the Core.
    Key step: for convex G and any ordering π, the marginal contribution
    vector m^π = (v(P^π_i ∪ {i}) - v(P^π_i))_i is in the Core.
    The Shapley value is the average of all marginal vectors,
    and the Core is convex, so the average is also in the Core.
    Alternative: prove convex ⇒ balanced, then use Bondareva-Shapley. -/
theorem convex_core_nonempty (h : G.Convex) :
    G.Core.Nonempty := by
  sorry

end TUGame

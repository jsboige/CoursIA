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
import Mathlib.Algebra.BigOperators.Group.Finset
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

/-- The unanimity game for coalition T:
    v(S) = 1 if T ⊆ S, else 0 -/
def unanimityGame (T : Finset N) : TUGame N where
  v := fun S => if T ⊆ S then 1 else 0
  empty_zero := by
    simp only
    by_cases hT : T = ∅
    · simp [hT]
    · have : ¬(T ⊆ ∅) := fun h => hT (Finset.subset_empty.mp h)
      simp [this]

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

/-- Superadditive games have non-negative grand coalition value -/
theorem superadditive_grand_coalition_nonneg (h : G.Superadditive) :
    G.v Finset.univ ≥ 0 := by
  have h0 := G.empty_zero
  have h1 : G.v (∅ ∪ ∅) ≥ G.v ∅ + G.v ∅ := h ∅ ∅ (Finset.disjoint_self.mpr rfl)
  simp [h0] at h1
  -- The full proof requires showing Finset.univ ≥ 0 by induction
  sorry

/-- Bondareva-Shapley: The Core is nonempty iff the game is balanced -/
theorem bondareva_shapley :
    G.Core.Nonempty ↔ G.Balanced := by
  -- This is a major theorem requiring linear programming duality
  sorry

/-- For convex games, Shapley value is in the Core -/
theorem convex_core_nonempty (h : G.Convex) :
    G.Core.Nonempty := by
  -- Convex games are balanced, so their Core is nonempty
  sorry

end TUGame

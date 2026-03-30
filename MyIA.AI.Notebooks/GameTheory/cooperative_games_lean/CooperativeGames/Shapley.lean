/-
  Shapley Value - Axiomatic Characterization
  ==========================================

  This file formalizes Shapley's axiomatic approach to fair division:
  - The four Shapley axioms (Efficiency, Symmetry, Null player, Additivity)
  - The Shapley value formula
  - Uniqueness theorem

  Reference: L.S. Shapley, "A Value for N-Person Games" (1953)
-/

import CooperativeGames.Basic

open TUGame

variable {N : Type*} [Fintype N] [DecidableEq N]

/-! ## Solutions and Axioms -/

/-- A solution concept assigns to each game a payoff vector -/
def Solution (N : Type*) [Fintype N] := TUGame N → (N → ℝ)

namespace Solution

variable (φ : Solution N)

/-! ## The Four Shapley Axioms -/

/-- Axiom 1: Efficiency
    The payoffs sum to the value of the grand coalition -/
def Efficiency : Prop :=
  ∀ G : TUGame N, ∑ i : N, φ G i = G.v Finset.univ

/-- Two players are symmetric in G if they make equal contributions -/
def SymmetricPlayers (G : TUGame N) (i j : N) : Prop :=
  ∀ S : Finset N, i ∉ S → j ∉ S →
    G.v (S ∪ {i}) = G.v (S ∪ {j})

/-- Axiom 2: Symmetry
    Symmetric players receive equal payoffs -/
def Symmetry : Prop :=
  ∀ G : TUGame N, ∀ i j : N,
    SymmetricPlayers G i j → φ G i = φ G j

/-- A player i is null if they add no value to any coalition -/
def NullPlayer (G : TUGame N) (i : N) : Prop :=
  ∀ S : Finset N, i ∉ S →
    G.v (S ∪ {i}) = G.v S

/-- Axiom 3: Null Player
    A player with no marginal contribution receives 0 -/
def NullPlayerAxiom : Prop :=
  ∀ G : TUGame N, ∀ i : N,
    NullPlayer G i → φ G i = 0

/-- Sum of two TU games -/
def AddGames (G H : TUGame N) : TUGame N where
  v := fun S => G.v S + H.v S
  empty_zero := by simp [G.empty_zero, H.empty_zero]

/-- Axiom 4: Additivity
    The solution of a sum of games equals the sum of solutions -/
def Additivity : Prop :=
  ∀ G H : TUGame N, ∀ i : N,
    φ (AddGames G H) i = φ G i + φ H i

end Solution

/-! ## The Shapley Value -/

/-- The Shapley coefficient for a coalition of size s in a game with n players:
    c(s,n) = s! * (n - s - 1)! / n! -/
noncomputable def shapleyCoef (n s : ℕ) : ℝ :=
  (Nat.factorial s * Nat.factorial (n - s - 1)) / Nat.factorial n

/-- The Shapley value: average marginal contribution over all orderings -/
noncomputable def shapleyValue (G : TUGame N) (i : N) : ℝ :=
  ∑ S ∈ (Finset.univ.filter fun S => i ∉ S),
    shapleyCoef (Fintype.card N) S.card * G.marginalContribution i S

/-- The Shapley solution concept -/
noncomputable def shapleySolution : Solution N :=
  fun G i => shapleyValue G i

/-! ## Key Properties -/

namespace ShapleyValue

/-- Shapley value satisfies the null player axiom -/
theorem shapley_null_player (G : TUGame N) (i : N)
    (h : Solution.NullPlayer G i) : shapleyValue G i = 0 := by
  unfold shapleyValue
  apply Finset.sum_eq_zero
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  have hmc : G.marginalContribution i S = 0 := by
    unfold TUGame.marginalContribution
    rw [h S hS]
    ring
  simp [hmc]

/-- Shapley value for unanimity games:
    φᵢ(uₜ) = 1/|T| if i ∈ T, else 0 -/
theorem shapley_unanimity (T : Finset N) (i : N) :
    shapleyValue (TUGame.unanimityGame T) i =
    if i ∈ T then (1 : ℝ) / T.card else 0 := by
  -- The proof uses the fact that i contributes only when
  -- the coalition contains all of T \ {i}
  sorry

/-- Shapley value satisfies efficiency -/
theorem shapley_efficient (G : TUGame N) :
    ∑ i : N, shapleyValue G i = G.v Finset.univ := by
  -- Sum over all orderings, each marginal contribution counted once
  sorry

/-- Shapley value satisfies symmetry -/
theorem shapley_symmetric (G : TUGame N) (i j : N)
    (h : Solution.SymmetricPlayers G i j) :
    shapleyValue G i = shapleyValue G j := by
  -- Symmetric players have the same marginal contributions
  sorry

/-- Shapley value satisfies additivity -/
theorem shapley_additive (G H : TUGame N) (i : N) :
    shapleyValue (Solution.AddGames G H) i =
    shapleyValue G i + shapleyValue H i := by
  -- Linearity of summation
  unfold shapleyValue Solution.AddGames TUGame.marginalContribution
  simp only
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

end ShapleyValue

/-! ## Uniqueness Theorem -/

/-- Shapley's Uniqueness Theorem:
    The Shapley value is the unique solution satisfying all four axioms -/
theorem shapley_uniqueness (φ : Solution N)
    (h_eff : φ.Efficiency)
    (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (h_add : φ.Additivity) :
    ∀ G : TUGame N, ∀ i : N, φ G i = shapleyValue G i := by
  intro G i
  -- The proof proceeds by:
  -- 1. Decompose G into a sum of unanimity games: G = ∑_T cₜ * uₜ
  -- 2. Use additivity to reduce to unanimity games
  -- 3. Use efficiency, symmetry, and null player to determine φ(uₜ)
  -- 4. Show φ(uₜ) matches shapleyValue
  sorry

/-! ## Voting Games -/

/-- A weighted voting game [q; w₁, ..., wₙ] -/
def WeightedVotingGame (weights : N → ℝ) (quota : ℝ) : TUGame N where
  v := fun S => if ∑ i ∈ S, weights i ≥ quota then 1 else 0
  empty_zero := by simp

/-- Player i is critical in coalition S if removing them causes S to lose -/
def Critical (G : TUGame N) (i : N) (S : Finset N) : Prop :=
  i ∈ S ∧ G.v S = 1 ∧ G.v (S.erase i) = 0

/-- Raw Banzhaf index: number of coalitions where i is critical -/
def BanzhafRaw (G : TUGame N) (i : N) : ℕ :=
  (Finset.univ.filter fun S => Critical G i S).card

/-- Player with veto power -/
def VetoPlayer (G : TUGame N) (i : N) : Prop :=
  ∀ S : Finset N, G.v S = 1 → i ∈ S

/-- Dictator: can win alone and has veto -/
def Dictator (G : TUGame N) (i : N) : Prop :=
  G.v {i} = 1 ∧ VetoPlayer G i

/-- Dummy player: adds no value -/
def DummyPlayer (G : TUGame N) (i : N) : Prop :=
  ∀ S : Finset N, i ∉ S → G.v (S ∪ {i}) = G.v S

/-- Dummy players have zero Shapley value -/
theorem dummy_shapley_zero (G : TUGame N) (i : N) (h : DummyPlayer G i) :
    shapleyValue G i = 0 :=
  ShapleyValue.shapley_null_player G i h

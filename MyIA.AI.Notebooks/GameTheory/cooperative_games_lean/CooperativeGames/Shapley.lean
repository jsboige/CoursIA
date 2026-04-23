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
    φᵢ(uₜ) = 1/|T| if i ∈ T, else 0
    PROOF SKETCH:
    Case i ∉ T: i is a null player in u_T, so φᵢ = 0 by shapley_null_player.
      Null player proof: v(S∪{i}) = (if T⊆S∪{i} then 1 else 0).
      Since i ∉ T, T⊆S∪{i} ↔ T⊆S. So v(S∪{i}) = v(S).
    Case i ∈ T: By symmetry (shapley_symmetric), all j ∈ T have equal value.
      By efficiency (shapley_efficient), sum = v(univ) = 1.
      So each gets 1/|T|.
      Direct argument: marginalContribution i S = 1 iff T\{i} ⊆ S and i ∉ S.
      Count such S of size s: C(n-|T|-1+1, s-|T|+1) ... leads to 1/|T|. -/
theorem shapley_unanimity (T : Finset N) (i : N) :
    shapleyValue (TUGame.unanimityGame T) i =
    if i ∈ T then (1 : ℝ) / T.card else 0 := by
  sorry

/-- Shapley value satisfies efficiency.
    PROOF SKETCH:
    ∑ᵢ φᵢ(G) = ∑ᵢ ∑_{S:i∉S} c(|S|,n) · [v(S∪{i}) - v(S)]
    Swap order of summation:
    = ∑_S ∑_{i∉S} c(|S|,n) · [v(S∪{i}) - v(S)]
    = ∑_S c(|S|,n) · ∑_{i∉S} [v(S∪{i}) - v(S)]
    Each i ∉ S contributes its marginal value to S.
    Telescoping: ∑_{i∉S} v(S∪{i}) - (n-|S|)·v(S)
    After rearranging over all S, terms cancel to leave v(univ) - v(∅) = v(univ).
    The key identity: each v(S) appears as +v(S) with coefficient c(|S|-1,n)
    and as -v(S) with coefficient c(|S|,n)·(n-|S|), which cancel. -/
theorem shapley_efficient (G : TUGame N) :
    ∑ i : N, shapleyValue G i = G.v Finset.univ := by
  sorry

/-- Shapley value satisfies symmetry.
    PROOF SKETCH (swap bijection):
    Define f : {S | i ∉ S} → {T | j ∉ T} by:
    - f(S) = S                    if j ∉ S (both i,j absent)
    - f(S) = (S\{j})∪{i}        if j ∈ S (swap j for i)

    Properties:
    (1) |f(S)| = |S|, so shapleyCoef n |f(S)| = shapleyCoef n |S|
    (2) v(f(S)∪{j}) - v(f(S)) = v(S∪{i}) - v(S):
      - Case j ∉ S: f(S)=S, marginalContribution j S = v(S∪{j})-v(S) = v(S∪{i})-v(S)
        (by h with i,j both ∉ S)
      - Case j ∈ S: f(S)=(S\{j})∪{i}, f(S)∪{j}=S∪{i}, and
        v(f(S)) = v((S\{j})∪{i}) = v((S\{j})∪{j}) = v(S)
        (by h applied to S' = S\{j}, since i∉S\{j} and j∉S\{j})
    (3) f is a bijection (inverse: swap i↔j)

    Use Finset.sum_bij to conclude ∑_S g(S) = ∑_T g'(T). -/
theorem shapley_symmetric (G : TUGame N) (i j : N)
    (h : Solution.SymmetricPlayers G i j) :
    shapleyValue G i = shapleyValue G j := by
  by_cases heq : i = j
  · subst heq; rfl
  unfold shapleyValue TUGame.marginalContribution
  haveI : DecidableEq N := Classical.decEq _
  -- TODO: Formalize the swap bijection using Finset.sum_bij
  -- Key lemma needed: swap_preserves_marginal
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
    The Shapley value is the unique solution satisfying all four axioms.
    PROOF SKETCH (standard textbook, e.g. Roth 1988):
    1. Decompose: any game G = ∑_T cₜ · u_T (sum of unanimity games),
       where cₜ = ∑_{S⊆T} (-1)^|T\|S| · v(S) (Mobius inversion).
    2. By additivity: φ(G) = ∑_T cₜ · φ(u_T).
    3. For u_T with |T| = k:
       - Null player axiom: φᵢ(u_T) = 0 for i ∉ T (null player in u_T)
       - Symmetry axiom: all k players in T get the same value
       - Efficiency axiom: k · φᵢ(u_T) = 1, so φᵢ(u_T) = 1/k
    4. This matches the Shapley value formula for u_T.
    KEY DEPENDENCY: Requires shapley_unanimity, shapley_efficient,
    shapley_symmetric, shapley_null_player, and the Mobius decomposition. -/
theorem shapley_uniqueness (φ : Solution N)
    (h_eff : φ.Efficiency)
    (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (h_add : φ.Additivity) :
    ∀ G : TUGame N, ∀ i : N, φ G i = shapleyValue G i := by
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

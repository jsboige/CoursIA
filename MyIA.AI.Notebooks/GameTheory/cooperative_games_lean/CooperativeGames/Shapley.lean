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
theorem shapley_unanimity (T : Finset N) (hT : T.Nonempty) (i : N) :
    shapleyValue (TUGame.unanimityGame T hT) i =
    if i ∈ T then (1 : ℝ) / T.card else 0 := by
  classical
  split_ifs with hiT
  · -- Case i ∈ T: direct computation
    -- marginal contribution = 1 iff T\{i} ⊆ S (and i ∉ S, given by filter)
    -- = ∑_{S : i∉S, T\{i} ⊆ S} c(|S|, n) = 1/|T|
    unfold shapleyValue TUGame.marginalContribution shapleyCoef
    simp only [TUGame.unanimityGame]
    -- marginal = if T ⊆ S∪{i} then 1 else 0 - if T ⊆ S then 1 else 0
    -- Since i ∈ T: T ⊆ S∪{i} iff T\{i} ⊆ S (i is in T and in S∪{i})
    -- And ¬(T ⊆ S) since i ∉ S and i ∈ T
    -- So marginal = 1 iff T\{i} ⊆ S
    sorry
  · -- Case i ∉ T: i is a null player in unanimityGame T
    apply ShapleyValue.shapley_null_player
    intro S hiS
    simp only [TUGame.unanimityGame]
    -- T ⊆ S ∪ {i} iff T ⊆ S since i ∉ T
    have hto : T ⊆ S ∪ {i} → T ⊆ S := fun h j hj => by
      obtain hj' | hj' := Finset.mem_union.mp (h hj)
      · exact hj'
      · exact absurd (Finset.mem_singleton.mp hj') (fun heq => hiT (heq ▸ hj))
    split_ifs
    · rfl
    · exfalso; exact ‹¬T ⊆ S› (hto ‹T ⊆ S ∪ {i}›)
    · exfalso; exact ‹¬T ⊆ S ∪ {i}› (fun j hj => Finset.mem_union_left {i} (‹T ⊆ S› hj))
    · rfl

/-! ## Helper lemmas for efficiency proof -/

private theorem shapleyCoef_shift (n s : ℕ) (hs : s + 2 ≤ n) :
    (s + 1 : ℝ) * shapleyCoef n s = (n - s - 1 : ℝ) * shapleyCoef n (s + 1) := by
  unfold shapleyCoef
  rw [← mul_div_assoc, ← mul_div_assoc]
  congr 1
  rw [show n - (s + 1) - 1 = n - s - 2 from by omega]
  rw [Nat.factorial_succ s]
  have hm : n - s - 1 = (n - s - 2) + 1 := by omega
  rw [hm, Nat.factorial_succ (n - s - 2)]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  -- Convert ↑(n - s - 2) to ↑n - ↑s - 2 using Nat subtraction cast lemmas
  rw [Nat.cast_sub (by omega : (2 : ℕ) ≤ n - s)]
  rw [Nat.cast_sub (by omega : (s : ℕ) ≤ n)]
  ring

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
  classical
  unfold shapleyValue TUGame.marginalContribution
  -- Swap: ∑ᵢ ∑_{S:i∉S} f(i,S) = ∑_S ∑_{i:i∉S} f(i,S)
  have hswap :
    (∑ i ∈ Finset.univ, ∑ S ∈ Finset.univ.filter (fun S => i ∉ S),
        shapleyCoef (Fintype.card N) S.card * (G.v (S ∪ {i}) - G.v S)) =
    (∑ S ∈ Finset.univ, ∑ i ∈ Finset.univ.filter (fun i => i ∉ S),
        shapleyCoef (Fintype.card N) S.card * (G.v (S ∪ {i}) - G.v S)) :=
    Finset.sum_comm' (fun i S => by simp)
  rw [hswap]
  -- Factor shapleyCoef out of inner sum
  simp only [← Finset.mul_sum]
  -- Split subtraction in inner sums: ∑ (a - b) = ∑ a - ∑ b
  simp only [Finset.sum_sub_distrib]
  -- Distribute mul_sub inside the sum
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  -- Simplify negative term: v(x) constant in x_1, sum = (n - |x|) • v(x)
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp only [← Finset.sdiff_eq_filter, Finset.card_univ_diff]
  trace_state
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
  classical
  by_cases heq : i = j
  · subst heq; rfl
  -- Swap bijection proof using Finset.sum_bij
  -- The forward function maps {S | i ∉ S} → {T | j ∉ T} by swapping j↔i
  unfold shapleyValue TUGame.marginalContribution
  set src := Finset.univ.filter (fun S : Finset N => i ∉ S)
  set tgt := Finset.univ.filter (fun S : Finset N => j ∉ S)
  have hmem_src {S} : S ∈ src ↔ i ∉ S := by simp [src]
  have hmem_tgt {T} : T ∈ tgt ↔ j ∉ T := by simp [tgt]
  -- Define the forward and inverse as separate definitions so they reduce properly
  let fwd (S : Finset N) (_ : S ∈ src) : Finset N :=
    if hSj : j ∈ S then (S.erase j) ∪ {i} else S
  let inv (T : Finset N) (_ : T ∈ tgt) : Finset N :=
    if hTi : i ∈ T then (T.erase i) ∪ {j} else T
  refine Finset.sum_bij' fwd inv ?fwd_mem ?inv_mem ?left_inv ?right_inv ?hfg
  case fwd_mem =>
    intro S hS
    rw [hmem_src] at hS
    rw [hmem_tgt]
    -- Goal: j ∉ fwd S hS✝ where fwd S _ = if j ∈ S then (S.erase j) ∪ {i} else S
    simp only [fwd]
    split_ifs with hSj
    · -- fwd = (S.erase j) ∪ {i}, prove j ∉ (S.erase j) ∪ {i}
      rw [Finset.mem_union]
      intro h
      rcases h with h | h
      · exact Finset.notMem_erase j S h
      · exact heq (Finset.mem_singleton.mp h).symm
    · exact hSj
  case inv_mem =>
    intro T hT
    rw [hmem_tgt] at hT
    rw [hmem_src]
    simp only [inv]
    split_ifs with hTi
    · -- inv = (T.erase i) ∪ {j}, prove i ∉ (T.erase i) ∪ {j}
      rw [Finset.mem_union]
      intro h
      rcases h with h | h
      · exact Finset.notMem_erase i T h
      · exact heq (Finset.mem_singleton.mp h)
    · exact hTi
  case left_inv =>
    intro S hS
    rw [hmem_src] at hS
    dsimp only [fwd, inv]
    split_ifs with hSj hTi
    · -- j ∈ S, i ∈ (S.erase j) ∪ {i}: the real case
      have hnI : i ∉ S.erase j := fun h' => hS (Finset.mem_of_mem_erase h')
      have : ((S.erase j) ∪ {i}).erase i = S.erase j := by
        rw [Finset.erase_union_distrib]
        simp [Finset.erase_eq_self.mpr hnI]
      rw [this, Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hSj]
    · -- j ∈ S, i ∉ (S.erase j) ∪ {i}: impossible
      exact absurd (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))) hTi
    · -- j ∉ S: fwd(S) = S, inner condition i ∈ S auto-closed by hS, identity
      rfl
  case right_inv =>
    intro T hT
    rw [hmem_tgt] at hT
    dsimp only [fwd, inv]
    split_ifs with hSj hTi
    · -- hSj : i ∈ T, hTi : j ∈ T.erase i ∪ {j}: the real case
      have hnJ : j ∉ T.erase i := fun h => hT (Finset.mem_of_mem_erase h)
      have : ((T.erase i) ∪ {j}).erase j = T.erase i := by
        rw [Finset.erase_union_distrib]
        simp [Finset.erase_eq_self.mpr hnJ]
      rw [this, Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hSj]
    · -- hSj : i ∈ T, hTi : j ∉ T.erase i ∪ {j}: impossible
      exact absurd (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))) hTi
    · -- i ∉ T: inv(T) = T, inner condition j ∈ T auto-closed by hT, identity
      rfl
  case hfg =>
    intro S hS
    rw [hmem_src] at hS
    dsimp only [fwd]
    split_ifs with hSj
    · -- j ∈ S: fwd(S) = (S.erase j) ∪ {i}
      have hnI : i ∉ S.erase j := fun h' => hS (Finset.mem_of_mem_erase h')
      have hcard : ((S.erase j) ∪ {i} : Finset N).card = S.card := by
        have hge : 0 < S.card := Finset.card_pos.mpr ⟨j, hSj⟩
        rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hnI),
          Finset.card_erase_of_mem hSj, Finset.card_singleton]
        omega
      simp only [hcard]
      have hv1 : G.v (S ∪ {i}) = G.v ((S.erase j) ∪ {i} ∪ {j}) := by
        congr 1
        rw [Finset.union_assoc, Finset.union_comm {i} {j}, ← Finset.union_assoc,
          Finset.union_comm (S.erase j) {j}, ← Finset.insert_eq,
          Finset.insert_erase hSj]
      have hv2 : G.v S = G.v ((S.erase j) ∪ {i}) := by
        have hsym := h (S.erase j) hnI (Finset.notMem_erase j S)
        rw [hsym]
        congr 1
        rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hSj]
      rw [hv1, hv2]
    · -- j ∉ S: fwd(S) = S
      have hsym := h S hS hSj
      rw [hsym]

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

/-- A weighted voting game [q; w₁, ..., wₙ] with positive quota -/
noncomputable def WeightedVotingGame (weights : N → ℝ) (quota : ℝ) (hquota : 0 < quota) : TUGame N where
  v := fun S => if ∑ i ∈ S, weights i ≥ quota then 1 else 0
  empty_zero := by simp [hquota]

/-- Player i is critical in coalition S if removing them causes S to lose -/
def Critical (G : TUGame N) (i : N) (S : Finset N) : Prop :=
  i ∈ S ∧ G.v S = 1 ∧ G.v (S.erase i) = 0

/-- Raw Banzhaf index: number of coalitions where i is critical.
    Uses Classical.decPred since Critical involves noncomputable real comparisons. -/
noncomputable def BanzhafRaw (G : TUGame N) (i : N) : ℕ :=
  haveI : DecidablePred (fun S => Critical G i S) := Classical.decPred _
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

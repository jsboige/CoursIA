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
import Mathlib.Data.Nat.Choose.Sum

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

/-! ## Unanimity Game Characterization (any axiom-satisfying solution) -/

/-- Any efficient symmetric null-player-respecting solution gives 1/|T|
    for players in T and 0 for players outside T in the unanimity game u_T.
    Uses the three axioms (efficiency, symmetry, null player) directly. -/
private theorem phi_unanimity (φ : Solution N)
    (h_eff : φ.Efficiency)
    (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (T : Finset N) (hT : T.Nonempty) (i : N) :
    φ (TUGame.unanimityGame T hT) i =
    if i ∈ T then (1 : ℝ) / T.card else 0 := by
  classical
  split_ifs with hiT
  · -- Case i ∈ T: by symmetry all j∈T get same value, by efficiency sum=1
    -- Step 1: By symmetry, all j ∈ T have the same value as i
    have h_eq : ∀ j ∈ T, φ (unanimityGame T hT) j = φ (unanimityGame T hT) i := by
      intro j hjT
      by_cases hij : j = i; · subst hij; rfl
      · apply h_sym
        intro S hiS hjS
        simp only [unanimityGame]
        have hni : ¬(T ⊆ S ∪ {i}) := by
          intro h
          have := h hjT
          simp only [Finset.mem_union, Finset.mem_singleton] at this
          tauto
        have hnj : ¬(T ⊆ S ∪ {j}) := by
          intro h
          have := h hiT
          simp only [Finset.mem_union, Finset.mem_singleton] at this
          tauto
        rw [if_neg hni, if_neg hnj]
    -- Step 2: Players outside T are null
    have h_null_out : ∀ j, j ∉ T → φ (unanimityGame T hT) j = 0 := by
      intro j hjT'
      apply h_null
      intro S hjS
      simp only [unanimityGame]
      have hto : T ⊆ S ∪ {j} → T ⊆ S := fun h k hk => by
        have hk' := h hk
        simp only [Finset.mem_union, Finset.mem_singleton] at hk'
        rcases hk' with hk' | hk'
        · exact hk'
        · subst hk'; exact absurd hk hjT'
      split_ifs
      · rfl
      · exfalso; exact ‹¬T ⊆ S› (hto ‹T ⊆ S ∪ {j}›)
      · exfalso; exact ‹¬T ⊆ S ∪ {j}› (fun k hk => Finset.mem_union_left {j} (‹T ⊆ S› hk))
      · rfl
    -- Step 3: Efficiency: sum = v(univ) = 1
    have h_sum_one : ∑ j, φ (unanimityGame T hT) j = 1 := by
      have := h_eff (unanimityGame T hT)
      simp only [unanimityGame, if_pos (Finset.subset_univ T)] at this
      exact this
    -- Step 4: ∑_{∈T} = 1 (since ∑_{∉T} = 0)
    have h_sum_T : ∑ j ∈ T, φ (unanimityGame T hT) j = 1 := by
      have h_out_sum : ∑ j ∈ Finset.filter (fun j => j ∉ T) Finset.univ,
          φ (unanimityGame T hT) j = 0 :=
        Finset.sum_eq_zero (fun j hj => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact h_null_out j hj)
      have h_split : ∑ j ∈ T, φ (unanimityGame T hT) j +
          ∑ j ∈ Finset.filter (fun j => j ∉ T) Finset.univ,
          φ (unanimityGame T hT) j = ∑ j, φ (unanimityGame T hT) j := by
        have : Finset.filter (fun j => j ∉ T) Finset.univ = Tᶜ := by
          ext j; simp
        rw [this]
        rw [Finset.sum_add_sum_compl T (fun j => φ (unanimityGame T hT) j)]
      linarith
    -- Step 5: All equal in T, so T.card * φ G i = 1
    have h_card : (T.card : ℝ) * φ (unanimityGame T hT) i = 1 := by
      have : ∑ _ ∈ T, φ (unanimityGame T hT) i = (T.card : ℝ) * φ (unanimityGame T hT) i := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [← this]
      exact (Finset.sum_congr rfl (fun j hj => (h_eq j hj).symm)).trans h_sum_T
    -- Step 6: Therefore φ G i = 1 / T.card
    have hT0 : (T.card : ℝ) ≠ 0 := by
      have hcp : 0 < T.card := Finset.Nonempty.card_pos hT
      norm_cast
      omega
    field_simp
    linarith
  · -- Case i ∉ T: i is a null player in unanimityGame T
    apply h_null
    intro S hiS
    simp only [TUGame.unanimityGame]
    have hto : T ⊆ S ∪ {i} → T ⊆ S := fun h j hj => by
      obtain hks | hki := Finset.mem_union.mp (h hj)
      · exact hks
      · exact absurd (Finset.mem_singleton.mp hki) (fun heq => hiT (heq ▸ hj))
    split_ifs <;> try rfl
    · exfalso; exact ‹¬T ⊆ S› (hto ‹T ⊆ S ∪ {i}›)
    · exfalso; exact ‹¬T ⊆ S ∪ {i}› (fun j hj => Finset.mem_union_left {i} (‹T ⊆ S› hj))

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

private theorem shapleyCoef_top (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * shapleyCoef n (n - 1) = 1 := by
  unfold shapleyCoef
  have h1 : n - (n - 1) - 1 = 0 := by omega
  simp only [h1, Nat.factorial_zero, Nat.cast_one, mul_one]
  -- Goal: ↑n * (↑(n-1).factorial / ↑n.factorial) = 1
  have hfact : (n : ℝ) * ↑(Nat.factorial (n - 1)) = ↑(Nat.factorial n) := by
    have hsucc : n = (n - 1) + 1 := by omega
    rw [hsucc, Nat.factorial_succ]
    simp [Nat.cast_mul]
  rw [← mul_div_assoc, hfact, div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]

private theorem pos_term_eq (G : TUGame N) :
    (∑ S, shapleyCoef (Fintype.card N) S.card * ∑ i ∈ Finset.univ \ S, G.v (S ∪ {i})) =
    (∑ T, (T.card : ℝ) * shapleyCoef (Fintype.card N) (T.card - 1) * G.v T) := by
  classical
  -- Step 1: Move coefficient inside inner sum on LHS
  simp only [Finset.mul_sum]
  -- Step 2: Prove pointwise: ↑|T| * c * v = ∑ j ∈ T, c * v
  have hT (T : Finset N) :
      (T.card : ℝ) * shapleyCoef (Fintype.card N) (T.card - 1) * G.v T =
      ∑ j ∈ (T : Finset N), shapleyCoef (Fintype.card N) (T.card - 1) * G.v T := by
    rw [mul_assoc, ← nsmul_eq_mul, ← Finset.sum_const]
  -- Step 3: Rewrite RHS using hT pointwise
  rw [Finset.sum_congr rfl (fun T _ => hT T)]
  -- Step 4: Flatten both sides to sigma sums, then apply bijection
  -- LHS: ∑ x, ∑ i ∈ univ\x, f(x,i) → ∑ p ∈ univ.sigma(fun x => univ\x), f(p.1,p.2)
  rw [Finset.sum_sigma']
  -- RHS: ∑ T, ∑ j ∈ T, g(T,j) → ∑ p ∈ univ.sigma(fun T => T), g(p.1,p.2)
  rw [Finset.sum_sigma']
  -- Now bijection on sigma types: (S, i) with i∉S ↦ (S∪{i}, i)
  -- f : (S, i) ↦ (S∪{i}, i), g : (T, j) ↦ (T\{j}, j)
  refine Finset.sum_bij' (fun p _ => ⟨p.1 ∪ {p.2}, p.2⟩)
      (fun p _ => ⟨p.1 \ {p.2}, p.2⟩) ?_ ?_ ?_ ?_ ?_
  -- f in range: p.2 ∈ p.1 ∪ {p.2}
  · intro p hp
    simp only [Finset.mem_sigma] at hp ⊢
    exact ⟨Finset.mem_univ _, by
      rw [Finset.union_comm]
      exact Finset.mem_insert_self _ _⟩
  -- g in range: p.2 ∈ univ \ (p.1 \ {p.2}) (i.e. p.2 ∉ p.1 \ {p.2})
  · intro p hp
    simp only [Finset.mem_sigma] at hp ⊢
    exact ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      intro h
      exact Finset.notMem_sdiff_of_mem_right (Finset.mem_singleton_self _) h⟩⟩
  -- g∘f = id: (S∪{i})\{i} = S when i∉S
  · intro p hp
    simp only [Finset.mem_sigma] at hp
    have hni : p.2 ∉ p.1 := (Finset.mem_sdiff.mp hp.2).2
    simp only
    -- goal: ⟨(p.fst ∪ {p.snd}) \ {p.snd}, p.snd⟩ = p
    ext1
    · exact Finset.union_sdiff_cancel_right (Finset.disjoint_singleton_right.mpr hni)
    · rfl
  -- f∘g = id: (T\{j})∪{j} = T when j∈T
  · intro p hp
    simp only [Finset.mem_sigma] at hp
    simp only
    ext1
    · rw [Finset.union_comm, ← Finset.insert_eq,
        (Finset.insert_sdiff_self_of_mem hp.2)]
    · rfl
  -- values agree: c(|S|) * v(S∪{i}) = c(|S∪{i}|-1) * v(S∪{i})
  · intro p hp
    simp only [Finset.mem_sigma] at hp
    have hni : p.2 ∉ p.1 := (Finset.mem_sdiff.mp hp.2).2
    have : p.1.card = (p.1 ∪ {p.2}).card - 1 := by
      rw [Finset.union_comm, ← Finset.insert_eq,
        Finset.card_insert_of_notMem hni, Nat.add_sub_cancel]
    simp only [this]

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
  -- Reindex positive term: ∑ S ∑_{i∉S} c(|S|)*v(S∪{i}) = ∑ T, |T|*c(|T|-1)*v(T)
  rw [pos_term_eq]
  -- Combine into single sum of differences
  rw [← Finset.sum_sub_distrib]
  -- Isolate the univ term: all T ≠ univ have zero coefficient (shapleyCoef_shift)
  have : ∑ x ∈ Finset.univ,
      (↑x.card * shapleyCoef (Fintype.card N) (x.card - 1) * G.v x -
        shapleyCoef (Fintype.card N) x.card * (↑(Fintype.card N - x.card) * G.v x)) =
      (↑(Finset.univ : Finset N).card *
        shapleyCoef (Fintype.card N) ((Finset.univ : Finset N).card - 1) * G.v Finset.univ -
        shapleyCoef (Fintype.card N) (Finset.univ : Finset N).card *
          (↑(Fintype.card N - (Finset.univ : Finset N).card) * G.v Finset.univ)) :=
    Finset.sum_eq_single (Finset.univ : Finset N)
      (fun T _ hT => by
        have hcard : T.card < (Finset.univ : Finset N).card :=
          Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hT)
        simp only [Finset.card_univ] at hcard
        rw [sub_eq_zero]
        by_cases hT0 : T.card = 0
        · -- T = ∅: both terms vanish because v(∅) = 0
          have : T = ∅ := Finset.card_eq_zero.mp hT0
          simp [this, G.empty_zero]
        · -- T ≠ ∅: coefficient shift applies
          have hTcard : 1 ≤ T.card := Nat.pos_of_ne_zero hT0
          have hshift := shapleyCoef_shift (Fintype.card N) (T.card - 1) (by omega)
          have h1 : (↑(T.card - 1) + 1 : ℝ) = ↑T.card := by
            norm_cast; exact Nat.sub_add_cancel hTcard
          have h2 : (T.card - 1 + 1 : ℕ) = T.card := Nat.sub_add_cancel hTcard
          have h3 : (↑(Fintype.card N) - ↑(T.card - 1) - 1 : ℝ) = ↑(Fintype.card N - T.card) := by
            have hle : T.card ≤ Fintype.card N := Finset.card_le_univ T
            rw [Nat.cast_sub hle, ← h1]
            ring
          rw [h1, h2, h3] at hshift
          rw [hshift]
          ring)
      (fun h => (h (Finset.mem_univ _)).elim)
  rw [this]
  -- Simplify: n - card univ = 0, so negative term vanishes
  simp only [Finset.card_univ, tsub_self, Nat.cast_zero]
  -- Positive term: n * c(n,n-1) * v(univ) = v(univ) since n * c(n,n-1) = 1
  by_cases hN : IsEmpty N
  · -- Empty case: both sides reduce to 0
    simp [G.empty_zero]
  · -- Nonempty case: shapleyCoef_top applies
    haveI : Nonempty N := not_isEmpty_iff.mp hN
    have hn : 0 < Fintype.card N := Fintype.card_pos_iff.mpr ⟨Classical.arbitrary N⟩
    rw [shapleyCoef_top (Fintype.card N) hn, one_mul]
    simp only [zero_mul, mul_zero, sub_zero]

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

/-- Shapley value on unanimity games: each player in T gets 1/|T| -/
theorem shapley_unanimity (T : Finset N) (hT : T.Nonempty) (i : N) :
    shapleyValue (TUGame.unanimityGame T hT) i =
    if i ∈ T then (1 : ℝ) / T.card else 0 := by
  classical
  split_ifs with hiT
  · -- Case i ∈ T: by symmetry all j∈T get same value, by efficiency sum=1
    have h : shapleySolution (TUGame.unanimityGame T hT) i =
        if i ∈ T then (1 : ℝ) / T.card else 0 :=
      phi_unanimity (φ := shapleySolution)
        shapley_efficient shapley_symmetric
        (fun G i => shapley_null_player G i) T hT i
    simp only [shapleySolution, if_pos hiT] at h
    exact h
  · -- Case i ∉ T: i is a null player in unanimityGame T
    apply shapley_null_player
    intro S hiS
    simp only [TUGame.unanimityGame]
    have hto : T ⊆ S ∪ {i} → T ⊆ S := fun h j hj => by
      obtain hj' | hj' := Finset.mem_union.mp (h hj)
      · exact hj'
      · exact absurd (Finset.mem_singleton.mp hj') (fun heq => hiT (heq ▸ hj))
    split_ifs
    · rfl
    · exfalso; exact ‹¬T ⊆ S› (hto ‹T ⊆ S ∪ {i}›)
    · exfalso; exact ‹¬T ⊆ S ∪ {i}› (fun j hj => Finset.mem_union_left {i} (‹T ⊆ S› hj))
    · rfl

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

/-! ## Scalar Multiplication and Finite Sums of Games -/

namespace Solution

/-- Scalar multiplication of a TU game by a real number -/
def SmulGame (c : ℝ) (G : TUGame N) : TUGame N where
  v := fun S => c * G.v S
  empty_zero := by simp [G.empty_zero]

/-- The zero TU game -/
def zeroGame : TUGame N where
  v := fun _ => 0
  empty_zero := rfl

/-- phi of the zero game is 0 (every player is null) -/
theorem phi_zero_game (φ : Solution N) (h_null : φ.NullPlayerAxiom) (i : N) :
    φ zeroGame i = 0 :=
  h_null zeroGame i (fun S _ => rfl)

/-- Sum of games indexed by a finset -/
noncomputable def finsetSumGames {ι : Type*} (s : Finset ι) (f : ι → TUGame N) : TUGame N where
  v := fun S => ∑ j ∈ s, (f j).v S
  empty_zero := Finset.sum_eq_zero (fun j _ => (f j).empty_zero)

/-- Inserting into finsetSumGames gives AddGames -/
theorem finsetSumGames_insert {ι : Type*} [DecidableEq ι] {j : ι} {s : Finset ι}
    (f : ι → TUGame N) (hjs : j ∉ s) :
    finsetSumGames (insert j s) f = AddGames (finsetSumGames s f) (f j) := by
  ext S
  simp only [finsetSumGames, AddGames, Finset.sum_insert hjs]
  ring

end Solution

/-! ## Finite Additivity for Shapley Value -/

namespace ShapleyValue

/-- shapleyValue is homogeneous: shapleyValue (SmulGame c G) i = c * shapleyValue G i -/
theorem shapley_smulGame (c : ℝ) (G : TUGame N) (i : N) :
    shapleyValue (Solution.SmulGame c G) i = c * shapleyValue G i := by
  have hSmul : (Solution.SmulGame c G).v = fun S => c * G.v S := rfl
  unfold shapleyValue TUGame.marginalContribution
  rw [hSmul]
  have hLHS : (fun S => shapleyCoef (Fintype.card N) S.card *
        (c * G.v (S ∪ {i}) - c * G.v S)) =
      (fun S => c * (shapleyCoef (Fintype.card N) S.card *
        (G.v (S ∪ {i}) - G.v S))) := by
    funext S; ring
  simp only [hLHS]
  rw [Finset.mul_sum]

/-- Shapley value is additive -/
theorem shapley_addGames (G H : TUGame N) (i : N) :
    shapleyValue (Solution.AddGames G H) i = shapleyValue G i + shapleyValue H i := by
  unfold shapleyValue TUGame.marginalContribution
  simp only [Solution.AddGames]
  have h_key (S : Finset N) :
      shapleyCoef (Fintype.card N) S.card * (G.v (S ∪ {i}) + H.v (S ∪ {i}) - (G.v S + H.v S))
      = shapleyCoef (Fintype.card N) S.card * (G.v (S ∪ {i}) - G.v S)
        + shapleyCoef (Fintype.card N) S.card * (H.v (S ∪ {i}) - H.v S) := by ring
  rw [Finset.sum_congr rfl (fun S _ => h_key S), Finset.sum_add_distrib]

end ShapleyValue

/-! ## Mobius Inversion (Harsanyi Dividends) -/

namespace Mobius

/-- The Mobius coefficient (Harsanyi dividend) of game G for coalition T:
    a_T = Σ_{R ⊆ T} (-1)^{|T|-|R|} * G.v(R)
    This captures the "pure" value of coalition T beyond its subsets. -/
noncomputable def mobiusCoeff (G : TUGame N) (T : Finset N) : ℝ :=
  ∑ R ∈ Finset.univ.filter (fun R => R ⊆ T),
    ((-1 : ℝ) ^ (T.card - R.card)) * G.v R

/-- A game built from a weighted unanimity game -/
noncomputable def weightedUnanimity (c : ℝ) (T : Finset N) (hT : T.Nonempty) : TUGame N where
  v := fun S => c * (if T ⊆ S then (1 : ℝ) else 0)
  empty_zero := by
    simp only [Finset.subset_empty, if_neg hT.ne_empty, mul_zero]

/-- The Mobius reconstruction of G: G = Σ_{T≠∅} a_T • u_T -/
noncomputable def mobiusReconstruction (G : TUGame N) : TUGame N where
  v := fun S => ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ T ⊆ S),
      mobiusCoeff G T
  empty_zero := by
    classical
    apply Finset.sum_eq_zero
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨hne, hsub⟩ := hT
    have : T = ∅ := Finset.subset_empty.mp hsub
    rw [this] at hne
    exact absurd rfl hne.ne_empty

/-- Helper: for R ⊂ S, the alternating sum over supersets T of R within S is zero.
    Σ_{T : R ⊆ T ⊆ S} (-1)^(|T|-|R|) = (1-1)^|S\R| = 0 when S\R nonempty.
    Proof: bijection T ↦ T \ R to (S \ R).powerset, then sum_powerset_neg_one_pow_card. -/
private theorem mobius_inner_sum_zero (S R : Finset N) (hR : R ⊆ S) (hne : R ≠ S) :
    ∑ T ∈ Finset.univ.filter (fun T => R ⊆ T ∧ T ⊆ S),
        ((-1 : ℝ) ^ (T.card - R.card)) = 0 := by
  classical
  have hSR_ne : (S \ R).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    have h_sub : S ⊆ R := Finset.sdiff_eq_empty_iff_subset.mp h_empty
    exact hne (subset_antisymm hR h_sub)
  -- Reindex via bijection T ↦ T \ R to (S \ R).powerset
  have h_eq :
    ∑ T ∈ Finset.univ.filter (fun T => R ⊆ T ∧ T ⊆ S),
        ((-1 : ℝ) ^ (T.card - R.card)) =
    ∑ m ∈ (S \ R).powerset, ((-1 : ℝ) ^ m.card) := by
    refine Finset.sum_bij' (fun T _ => T \ R) (fun m _ => R ∪ m) ?_ ?_ ?_ ?_ ?_
    -- hi: forward map lands in target
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      obtain ⟨hRT, hTS⟩ := hT
      rw [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff hTS (Finset.Subset.refl R)
    -- hj: backward map lands in source
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Finset.mem_powerset] at hm
      exact ⟨Finset.subset_union_left,
             Finset.union_subset hR (hm.trans Finset.sdiff_subset)⟩
    -- left_inv: R ∪ (T \ R) = T
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      obtain ⟨hRT, _⟩ := hT
      show R ∪ (T \ R) = T
      rw [Finset.union_comm R (T \ R), Finset.sdiff_union_of_subset hRT]
    -- right_inv: (R ∪ m) \ R = m
    · intro m hm
      simp only [Finset.mem_powerset] at hm
      show (R ∪ m) \ R = m
      have h_disj : Disjoint R m := (Finset.subset_sdiff.mp hm).2.symm
      exact Finset.union_sdiff_cancel_left h_disj
    -- h: summand equality via card_sdiff_of_subset
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      obtain ⟨hRT, _⟩ := hT
      congr 1
      exact (Finset.card_sdiff_of_subset hRT).symm
  rw [h_eq]
  -- Rewrite: ∑ m ∈ powerset, (-1 : ℝ)^m.card = ↑(∑ m, (-1 : ℤ)^m.card)
  rw [show (∑ m ∈ (S \ R).powerset, ((-1 : ℝ) ^ m.card)) =
        ↑(∑ m ∈ (S \ R).powerset, ((-1 : ℤ) ^ m.card)) from by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun m _hm => ?_)
    have h_neg_one : (-1 : ℝ) = ↑(-1 : ℤ) := by rw [Int.cast_neg, Int.cast_one]
    rw [h_neg_one]
    exact (Int.cast_pow (-1 : ℤ) m.card).symm]
  rw [Finset.sum_powerset_neg_one_pow_card_of_nonempty hSR_ne, Int.cast_zero]

/-- Helper: for R = S, the inner sum is 1 (singleton {S} contributes (-1)^0 = 1). -/
private theorem mobius_inner_sum_self (S R : Finset N) (_hR : R ⊆ S) (hRS : R = S) :
    ∑ T ∈ Finset.univ.filter (fun T => R ⊆ T ∧ T ⊆ S),
        ((-1 : ℝ) ^ (T.card - R.card)) = 1 := by
  rw [hRS]
  have hSingleton : Finset.univ.filter (fun T => S ⊆ T ∧ T ⊆ S) = {S} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨hle, hge⟩ => le_antisymm hge hle,
           fun h => by rw [h]; exact ⟨Finset.Subset.refl S, Finset.Subset.refl S⟩⟩
  rw [hSingleton, Finset.sum_singleton, Nat.sub_self, pow_zero]

/-- Mobius inversion: v(S) = Σ_{∅≠T⊆S} a_T
    Every game decomposes uniquely into weighted unanimity games (Harsanyi dividends).
    Proof: inclusion-exclusion on the subset lattice.
    Σ_{T: ∅≠T⊆S} a_T = Σ_T Σ_{R⊆T} (-1)^(|T|-|R|) · v(R)
    After swapping sums: Σ_R v(R) · Σ_{T: R⊆T⊆S} (-1)^(|T|-|R|) = Σ_R v(R)·δ_{R,S} = v(S). -/
private theorem mobius_decomposition_axiom (G : TUGame N) (S : Finset N) :
    G.v S = ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ T ⊆ S),
        mobiusCoeff G T := by
  classical
  simp only [mobiusCoeff]
  -- Swap the order of summation
  have h_comm :
      ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ T ⊆ S),
          ∑ R ∈ Finset.univ.filter (fun R => R ⊆ T),
            ((-1 : ℝ) ^ (T.card - R.card)) * G.v R =
      ∑ R ∈ (Finset.univ : Finset (Finset N)),
          ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ R ⊆ T ∧ T ⊆ S),
            ((-1 : ℝ) ^ (T.card - R.card)) * G.v R :=
    Finset.sum_comm' (s := Finset.univ.filter (fun T => T.Nonempty ∧ T ⊆ S))
      (t := fun T => Finset.univ.filter (fun R => R ⊆ T))
      (t' := (Finset.univ : Finset (Finset N)))
      (s' := fun R => Finset.univ.filter (fun T => T.Nonempty ∧ R ⊆ T ∧ T ⊆ S))
      (fun T R => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact ⟨⟨h.1.1, h.2, h.1.2⟩, trivial⟩
        · intro h
          exact ⟨⟨h.1.1, h.1.2.2⟩, h.1.2.1⟩)
  rw [h_comm]
  -- Now show each R contributes either G.v R (if R = S) or 0 (otherwise)
  suffices h : ∀ R ∈ (Finset.univ : Finset (Finset N)),
      ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ R ⊆ T ∧ T ⊆ S),
          ((-1 : ℝ) ^ (T.card - R.card)) * G.v R =
        if R = S then G.v R else 0 by
    simp only [Finset.mem_univ, forall_true_left] at h
    simp_rw [h]
    -- ∑ R : Finset N, if R = S then G.v R else 0 = G.v S
    exact (Fintype.sum_ite_eq' S (fun R => G.v R)).symm
  intro R _hR
  by_cases hRS : R = S
  -- Case R = S
  · rw [if_pos hRS, hRS]
    by_cases hSe : S = ∅
    -- S = ∅: filter is empty, sum = 0 = G.v ∅
    · rw [hSe]
      have hFilter : (Finset.univ : Finset (Finset N)).filter
          (fun T => T.Nonempty ∧ (∅ : Finset N) ⊆ T ∧ T ⊆ (∅ : Finset N)) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem (fun T hT => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
        have hTe : T = ∅ := (Finset.subset_empty).mp hT.2.2
        subst hTe
        exact Finset.not_nonempty_empty hT.1
      rw [G.empty_zero, hFilter, Finset.sum_empty]
    -- S ≠ ∅: filter = {S}, sum = 1 * G.v S
    · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSe
      have hSingleton : Finset.univ.filter (fun T => T.Nonempty ∧ S ⊆ T ∧ T ⊆ S) = {S} := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun ⟨_, hST, hTS⟩ => le_antisymm hTS hST,
               fun h => by subst h; exact ⟨hSne, Finset.Subset.refl _, Finset.Subset.refl _⟩⟩
      rw [hSingleton, Finset.sum_singleton, Nat.sub_self, pow_zero, one_mul]
  -- Case R ≠ S
  · rw [if_neg hRS]
    by_cases hRsub : R ⊆ S
    -- Subcase R ⊆ S, R ≠ S
    · by_cases hRe : R = ∅
      -- R = ∅: G.v ∅ = 0
      · rw [hRe]
        simp [G.empty_zero]
      -- R ≠ ∅, R ⊆ S, R ≠ S
      · have hRne := Finset.nonempty_iff_ne_empty.mpr hRe
        have hfilter : Finset.univ.filter (fun T => T.Nonempty ∧ R ⊆ T ∧ T ⊆ S) =
            Finset.univ.filter (fun T => R ⊆ T ∧ T ⊆ S) := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun ⟨hTne, hRT, hTS⟩ => ⟨hRT, hTS⟩,
                 fun ⟨hRT, hTS⟩ => ⟨hRne.mono hRT, hRT, hTS⟩⟩
        rw [hfilter]
        have : ∑ T ∈ Finset.univ.filter (fun T => R ⊆ T ∧ T ⊆ S),
            ((-1 : ℝ) ^ (T.card - R.card)) * G.v R =
          (∑ T ∈ Finset.univ.filter (fun T => R ⊆ T ∧ T ⊆ S),
              ((-1 : ℝ) ^ (T.card - R.card))) * G.v R := by
          rw [Finset.sum_mul]
        rw [this, mobius_inner_sum_zero S R hRsub hRS, zero_mul]
    -- Subcase R ⊄ S: no T satisfies R ⊆ T ⊆ S
    · have hfilter : Finset.univ.filter (fun T => T.Nonempty ∧ R ⊆ T ∧ T ⊆ S) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem (fun T hT => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
        obtain ⟨_, hRT, hTS⟩ := hT
        exact hRsub (hRT.trans hTS)
      rw [hfilter, Finset.sum_empty]

theorem mobius_decomposition (G : TUGame N) (S : Finset N) :
    G.v S = ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ T ⊆ S),
        mobiusCoeff G T :=
  mobius_decomposition_axiom G S

end Mobius

/-! ## Uniqueness Theorem -/

/- Shapley's Uniqueness Theorem:
    The Shapley value is the unique solution satisfying all four axioms.
    Proof strategy: show any axiom-satisfying solution φ agrees with
    shapleyValue on unanimity games (phi_unanimity + phi_eq_shapley),
    then extend to all games via Mobius decomposition and additivity. -/

/-- φ agrees with shapleyValue on unanimity games -/
private theorem phi_eq_shapley (φ : Solution N)
    (h_eff : φ.Efficiency)
    (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (T : Finset N) (hT : T.Nonempty) (i : N) :
    φ (TUGame.unanimityGame T hT) i = shapleyValue (TUGame.unanimityGame T hT) i := by
  rw [phi_unanimity φ h_eff h_sym h_null T hT i,
      ShapleyValue.shapley_unanimity T hT i]

/-- Symmetry of players in T within SmulGame c u_T -/
private theorem sym_in_smulUnanimity (φ : Solution N)
    (h_sym : φ.Symmetry)
    (c : ℝ) (T : Finset N) (hT : T.Nonempty) (i j : N) (hiT : i ∈ T) (hjT : j ∈ T) (hij : i ≠ j) :
    φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i =
    φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j := by
  apply h_sym
  intro S hiS hjS
  simp only [Solution.SmulGame, TUGame.unanimityGame]
  have hni : ¬(T ⊆ S ∪ {i}) := by
    intro h; have := h hjT
    simp only [Finset.mem_union, Finset.mem_singleton] at this; tauto
  have hnj : ¬(T ⊆ S ∪ {j}) := by
    intro h; have := h hiT
    simp only [Finset.mem_union, Finset.mem_singleton] at this; tauto
  rw [if_neg hni, if_neg hnj]

/-- Null players outside T in SmulGame c u_T -/
private theorem null_outside_smulUnanimity (φ : Solution N)
    (h_null : φ.NullPlayerAxiom)
    (c : ℝ) (T : Finset N) (hT : T.Nonempty) (k : N) (hkT : k ∉ T) :
    φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) k = 0 :=
  h_null (Solution.SmulGame c (TUGame.unanimityGame T hT)) k
    (fun S _ => by
      simp only [Solution.SmulGame, TUGame.unanimityGame]
      have hto : T ⊆ S ∪ {k} → T ⊆ S := fun h m hm => by
        obtain hms | hmk := Finset.mem_union.mp (h hm)
        · exact hms
        · exact absurd (Finset.mem_singleton.mp hmk) (fun heq => hkT (heq ▸ hm))
      split_ifs <;> try rfl
      · exfalso; exact ‹¬T ⊆ S› (hto ‹T ⊆ S ∪ {k}›)
      · exfalso; exact ‹¬T ⊆ S ∪ {k}› (fun m hm => Finset.mem_union_left {k} (‹T ⊆ S› hm)))

/-- φ on a weighted unanimity game: φ(SmulGame c u_T, i) = c * φ(u_T, i).
    Proved directly from the axioms without general scalar multiplication. -/
private theorem phi_weightedUnanimity (φ : Solution N)
    (h_eff : φ.Efficiency)
    (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (c : ℝ) (T : Finset N) (hT : T.Nonempty) (i : N) :
    φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i = c * φ (TUGame.unanimityGame T hT) i := by
  classical
  rw [phi_unanimity φ h_eff h_sym h_null T hT i]
  split_ifs with hiT
  -- Case i ∈ T
  · -- Efficiency: Σ_j φ(H, j) = H.v(univ) = c
    have h_eff_T : ∑ j : N, φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j = c := by
      have h_val : (Solution.SmulGame c (TUGame.unanimityGame T hT)).v Finset.univ = c := by
        simp [Solution.SmulGame, TUGame.unanimityGame]
      exact (h_eff (Solution.SmulGame c (TUGame.unanimityGame T hT))).trans h_val
    -- Players outside T contribute 0
    have h_null_out : ∀ j, j ∉ T →
        φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j = 0 :=
      fun j hj => null_outside_smulUnanimity φ h_null c T hT j hj
    -- Sum over T complement = 0
    have h_out_sum : ∑ j ∈ Tᶜ, φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j = 0 :=
      Finset.sum_eq_zero (fun j hj => by
        simp only [Finset.mem_compl] at hj
        exact h_null_out j hj)
    -- ∑_{j∈T} φ(j) = c
    have h_sum_T : ∑ j ∈ T, φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j = c := by
      have h_split := Finset.sum_add_sum_compl T
          (fun j => φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j)
      linarith
    -- All players in T get the same value
    have h_eq : ∀ j ∈ T,
        φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j =
        φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i := by
      intro j hjT
      by_cases hij : j = i; · subst hij; rfl
      exact (sym_in_smulUnanimity φ h_sym c T hT i j hiT hjT (Ne.symm hij)).symm
    -- T.card * φ(H, i) = c
    have h_card : (T.card : ℝ) * φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i = c := by
      have : ∑ _ ∈ T, φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i =
          (T.card : ℝ) * φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [← this]
      exact (Finset.sum_congr rfl (fun j hj => (h_eq j hj).symm)).trans h_sum_T
    have hT0 : (T.card : ℝ) ≠ 0 := by
      have hcp : 0 < T.card := Finset.Nonempty.card_pos hT
      norm_cast; omega
    field_simp; linarith
  -- Case i ∉ T
  · rw [null_outside_smulUnanimity φ h_null c T hT i hiT]; ring

/-- Any axiom-satisfying φ agrees with shapleyValue on SmulGame c u_T -/
private theorem phi_eq_shapley_weighted (φ : Solution N)
    (h_eff : φ.Efficiency) (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (c : ℝ) (T : Finset N) (hT : T.Nonempty) (i : N) :
    φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i =
    shapleyValue (Solution.SmulGame c (TUGame.unanimityGame T hT)) i := by
  rw [phi_weightedUnanimity φ h_eff h_sym h_null c T hT i,
      ShapleyValue.shapley_smulGame c (TUGame.unanimityGame T hT) i,
      phi_eq_shapley φ h_eff h_sym h_null T hT i]

/-- φ distributes over finite sums (from binary Additivity by induction) -/
private theorem phi_finsetSumGames (φ : Solution N)
    (h_null : φ.NullPlayerAxiom) (h_add : φ.Additivity)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → TUGame N) (i : N) :
    φ (Solution.finsetSumGames s f) i = ∑ j ∈ s, φ (f j) i := by
  induction s using Finset.induction with
  | empty =>
    have h : Solution.finsetSumGames (∅ : Finset ι) f = Solution.zeroGame := by
      ext S; simp [Solution.finsetSumGames, Solution.zeroGame]
    simp [h, Solution.phi_zero_game φ h_null i]
  | insert j s hjs ih =>
    rw [Solution.finsetSumGames_insert f hjs, h_add, ih, Finset.sum_insert hjs]; ring

/-- Shapley value distributes over finite sums -/
private theorem shapley_finsetSumGames {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → TUGame N) (i : N) :
    shapleyValue (Solution.finsetSumGames s f) i = ∑ j ∈ s, shapleyValue (f j) i := by
  induction s using Finset.induction with
  | empty =>
    have h : Solution.finsetSumGames (∅ : Finset ι) f = Solution.zeroGame := by
      ext S; simp [Solution.finsetSumGames, Solution.zeroGame]
    rw [h]
    exact ShapleyValue.shapley_null_player Solution.zeroGame i (fun S _ => rfl)
  | insert j s hjs ih =>
    rw [Solution.finsetSumGames_insert f hjs, ShapleyValue.shapley_addGames, ih,
      Finset.sum_insert hjs]; ring

/-- The game G equals the finsetSumGames of its Mobius decomposition terms.
    G = ∑_{T≠∅} SmulGame (mobiusCoeff G T) (unanimityGame T) -/
private theorem game_eq_mobius_sum (G : TUGame N) :
    G = Solution.finsetSumGames
      (Finset.univ.filter Finset.Nonempty)
      (fun T => if hT : T.Nonempty then
        Solution.SmulGame (Mobius.mobiusCoeff G T) (TUGame.unanimityGame T hT)
      else Solution.zeroGame) := by
  ext S
  simp only [Solution.finsetSumGames]
  classical
  -- Step 1: For T ∈ filter Nonempty, f(T).v S = mobiusCoeff G T * (if T⊆S then 1 else 0)
  have h_term (T : Finset N) (hT : T ∈ Finset.univ.filter Finset.Nonempty) :
      (if hT' : T.Nonempty then
        Solution.SmulGame (Mobius.mobiusCoeff G T) (TUGame.unanimityGame T hT')
      else (Solution.zeroGame : TUGame N)).v S =
        Mobius.mobiusCoeff G T * (if T ⊆ S then (1 : ℝ) else 0) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    rw [dif_pos hT]
    simp only [Solution.SmulGame, TUGame.unanimityGame]
  -- Step 2: a * (if p then 1 else 0) = if p then a else 0
  have h_mul (T : Finset N) :
      Mobius.mobiusCoeff G T * (if T ⊆ S then (1 : ℝ) else 0) =
      (if T ⊆ S then Mobius.mobiusCoeff G T else (0 : ℝ)) := by
    split_ifs <;> ring
  -- Step 3: chain the equalities to get the filtered sum
  have h_rhs :
      ∑ T ∈ Finset.univ.filter Finset.Nonempty,
        (if hT : T.Nonempty then
          Solution.SmulGame (Mobius.mobiusCoeff G T) (TUGame.unanimityGame T hT)
        else (Solution.zeroGame : TUGame N)).v S =
      ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ T ⊆ S),
        Mobius.mobiusCoeff G T := by
    rw [Finset.sum_congr rfl h_term, Finset.sum_congr rfl (fun T _ => h_mul T)]
    rw [← Finset.sum_filter, Finset.filter_filter]
  exact (Mobius.mobius_decomposition_axiom G S).trans h_rhs.symm

/-- Shapley value uniqueness: any axiom-satisfying solution equals the Shapley value.
    Strategy: decompose G = ∑_{T≠∅} a_T · u_T via Mobius, then both φ and shapleyValue
    distribute over the sum and agree on each term by phi_eq_shapley_weighted. -/
theorem shapley_uniqueness (φ : Solution N)
    (h_eff : φ.Efficiency)
    (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (h_add : φ.Additivity) :
    ∀ G : TUGame N, ∀ i : N, φ G i = shapleyValue G i := by
  intro G i
  classical
  let idx : Finset (Finset N) := Finset.univ.filter Finset.Nonempty
  let g : Finset N → TUGame N := fun T =>
    if hT : T.Nonempty then
      Solution.SmulGame (Mobius.mobiusCoeff G T) (TUGame.unanimityGame T hT)
    else Solution.zeroGame
  have hG : G = Solution.finsetSumGames idx g := game_eq_mobius_sum G
  rw [hG, phi_finsetSumGames φ h_null h_add, shapley_finsetSumGames]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, idx] at hT
  simp only [g, dif_pos hT]
  exact phi_eq_shapley_weighted φ h_eff h_sym h_null (Mobius.mobiusCoeff G T) T hT i

/-! ## Voting Games -/

/-- A weighted voting game [q; w₁, ..., wₙ] with positive quota -/
noncomputable def WeightedVotingGame (weights : N → ℝ) (quota : ℝ) (hquota : 0 < quota) : TUGame N where
  v := fun S => if ∑ i ∈ S, weights i ≥ quota then 1 else 0
  empty_zero := by simp [hquota]

/-! ## Simple games

A *simple game* is a transferable-utility game whose characteristic function takes only
the values `0` (losing coalition) and `1` (winning coalition). This is the natural setting
for voting-power notions: `VetoPlayer`, `Dictator`, `Critical`, and the Banzhaf indices are
only meaningful under this constraint (otherwise `v S ∈ {0, 1}` fails and the Banzhaf
normalisation `2 ^ (|N| - 1)` no longer matches the range of `v`).

The `SimpleGame G` predicate packages the `v ∈ {0, 1}` constraint that the Veto/Dictator
axioms (architectural greenlight, cycle 73) will assume. -/
def SimpleGame (G : TUGame N) : Prop :=
  ∀ S : Finset N, G.v S = 0 ∨ G.v S = 1

/-- A `WeightedVotingGame` is simple: its characteristic function is an `if … then 1 else 0`,
so every coalition's value is `0` or `1`. -/
theorem weighted_voting_game_simple (weights : N → ℝ) (quota : ℝ) (hquota : 0 < quota) :
    SimpleGame (WeightedVotingGame weights quota hquota) := by
  intro S
  simp only [WeightedVotingGame]
  by_cases h : ∑ i ∈ S, weights i ≥ quota
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

namespace SimpleGame

/-- In a simple game, a value that is not `0` must be `1`. This is the contrapositive reader
    used by the Veto/Dictator theorems to upgrade `v S ≠ 0` into `v S = 1`. -/
theorem eq_one_of_ne_zero {G : TUGame N} (hG : SimpleGame G) (S : Finset N)
    (hne : G.v S ≠ 0) : G.v S = 1 :=
  (hG S).resolve_left hne

/-- In a simple game, a value that not `1` must be `0`. Symmetric reader. -/
theorem eq_zero_of_ne_one {G : TUGame N} (hG : SimpleGame G) (S : Finset N)
    (hne : G.v S ≠ 1) : G.v S = 0 :=
  (hG S).resolve_right hne

end SimpleGame

/-! ## Strong games

A *strong* (transferable-utility) game is the dual of a proper game: a coalition and its
complement cannot both be losing — `v S = 0 → v Sᶜ = 1`. For a simple game this says the
complement of a losing coalition is winning. Together with `ProperGame`, `StrongGame` defines
a *self-dual* (proper and strong) simple voting game. A weighted voting game is strong whenever
the quota does not exceed half the total weight. -/
def StrongGame (G : TUGame N) : Prop :=
  ∀ ⦃S : Finset N⦄, G.v S = 0 → G.v Sᶜ = 1

namespace StrongGame

/-- In a strong game, the complement of a losing coalition is winning. -/
theorem complement_wins {G : TUGame N} (hG : StrongGame G) {S : Finset N}
    (hlose : G.v S = 0) : G.v Sᶜ = 1 :=
  hG hlose

end StrongGame

/-- A weighted voting game whose quota does not exceed half the total weight is strong: if a
    coalition's weight falls short of the quota, the complementary coalition's weight meets it
    (the two complementary weights sum to the total, which is at least `2 * quota`), so the
    complement wins. No sign assumption on the weights is needed — a pure consequence of the
    quota-to-total ratio. -/
theorem weighted_voting_game_strong (weights : N → ℝ) (quota : ℝ) (hquota : 0 < quota)
    (hstrong : 2 * quota ≤ ∑ i, weights i) :
    StrongGame (WeightedVotingGame weights quota hquota) := by
  intro S hlose
  simp only [WeightedVotingGame] at hlose ⊢
  -- Decode `S` losing into its weight falling short of the quota: if it reached the quota the
  -- `if` would evaluate to `1`, contradicting `hlose : … = 0`.
  have hS : ∑ i ∈ S, weights i < quota := by
    by_contra hge
    push_neg at hge
    rw [if_pos hge] at hlose
    linarith
  -- The complementary coalition's weight is `total − ∑_S`, hence `≥ quota`.
  have hSc : ∑ i ∈ Sᶜ, weights i = ∑ i, weights i - ∑ i ∈ S, weights i := by
    rw [← Finset.sum_add_sum_compl S weights]; ring
  have hSc_ge : ∑ i ∈ Sᶜ, weights i ≥ quota := by rw [hSc]; linarith
  -- The complement reaches the quota, so its value is `1`.
  exact if_pos hSc_ge

/-! ## Monotone games

A *monotone* (transferable-utility) game is one where enlarging a coalition never
decreases its value: `S ⊆ T → v S ≤ v T`. For a simple game this specialises to the
up-set property of the winning coalitions — `S` winning and `S ⊆ T` implies `T` winning
— the defining feature of a *proper* simple voting game.

Together with `SimpleGame`, `MonotoneGame` packages the hypotheses the Veto/Dictator
power-index theorems assume (architectural greenlight, ai-01 cycle 75→76). -/
def MonotoneGame (G : TUGame N) : Prop :=
  ∀ ⦃S T : Finset N⦄, S ⊆ T → G.v S ≤ G.v T

namespace MonotoneGame

/-- In a monotone game, a larger coalition has at least as large a value. -/
theorem le_of_subset {G : TUGame N} (hG : MonotoneGame G) {S T : Finset N}
    (h : S ⊆ T) : G.v S ≤ G.v T :=
  hG h

/-- The winning coalitions of a monotone simple game form an up-set: enlarging a winning
    coalition keeps it winning.

    Monotonicity gives `v S ≤ v T` for `S ⊆ T`; since `v S = 1` and `SimpleGame` forces
    `v T ∈ {0, 1}`, this rules out `v T = 0`, leaving `v T = 1`. This is the defining
    property of a *proper* simple voting game and the bridge from `MonotoneGame` to the
    veto theory. -/
theorem winning_upward_closed {G : TUGame N} (hG : MonotoneGame G) (hG' : SimpleGame G)
    {S T : Finset N} (hST : S ⊆ T) (hwin : G.v S = 1) : G.v T = 1 := by
  -- Monotonicity: `v S ≤ v T`, and `v S = 1` so `1 ≤ v T`; with `v T ∈ {0,1}` this
  -- rules out `v T = 0`, hence `v T = 1`.
  apply SimpleGame.eq_one_of_ne_zero hG' T
  intro hzero
  have : (1 : ℝ) ≤ G.v T := hwin ▸ hG hST
  linarith

end MonotoneGame

/-- The losing coalitions of a monotone simple game form a down-set: shrinking a losing
    coalition keeps it losing. The dual of the winning up-set property: monotonicity gives
    `v S ≤ v T`, and `v T = 0` forces `v S ≤ 0 < 1`; `SimpleGame` then rules out `v S = 1`,
    leaving `v S = 0`. -/
theorem losing_downward_closed {G : TUGame N} (hG : MonotoneGame G) (hG' : SimpleGame G)
    {S T : Finset N} (hST : S ⊆ T) (hlose : G.v T = 0) : G.v S = 0 := by
  -- Monotonicity: `v S ≤ v T = 0`, so `v S ≤ 0 < 1`; `SimpleGame` then rules out `v S = 1`.
  apply SimpleGame.eq_zero_of_ne_one hG' S
  intro hone
  have : G.v S ≤ G.v T := MonotoneGame.le_of_subset hG hST
  linarith

/-- A weighted voting game with non-negative weights is monotone: enlarging a coalition
    adds non-negative weight, so the weight sum can only increase, hence `v` (an
    `if sum ≥ quota then 1 else 0`) cannot decrease. -/
theorem weighted_voting_game_monotone (weights : N → ℝ) (quota : ℝ) (hquota : 0 < quota)
    (hw : ∀ i, 0 ≤ weights i) :
    MonotoneGame (WeightedVotingGame weights quota hquota) := by
  intro S T hST
  have hsum : ∑ i ∈ S, weights i ≤ ∑ i ∈ T, weights i :=
    Finset.sum_le_sum_of_subset_of_nonneg hST (fun i _ _ => hw i)
  simp only [WeightedVotingGame]
  split_ifs with h₁ h₂
  · exact le_refl _                                   -- both reach quota: 1 ≤ 1
  · exact absurd (le_trans h₁ hsum) h₂               -- S reaches, T does not: impossible
  · exact zero_le_one                                 -- S does not, T does: 0 ≤ 1
  · exact le_refl _                                   -- neither: 0 ≤ 0

/-! ## Proper games

A *proper* (transferable-utility) game is one where a coalition and its complement cannot both
be winning: `v S = 1 → v Sᶜ = 0`. For a simple game this is the standard "no two complementary
coalitions both win" property of a proper simple voting game (the complement of a winning
coalition is losing). A weighted voting game is proper whenever the quota strictly exceeds half
the total weight, since the weights of complementary coalitions sum to the total. -/
def ProperGame (G : TUGame N) : Prop :=
  ∀ ⦃S : Finset N⦄, G.v S = 1 → G.v Sᶜ = 0

namespace ProperGame

/-- In a proper game, the complement of a winning coalition is losing. -/
theorem complement_loses {G : TUGame N} (hG : ProperGame G) {S : Finset N}
    (hwin : G.v S = 1) : G.v Sᶜ = 0 :=
  hG hwin

end ProperGame

/-- A weighted voting game whose quota strictly exceeds half the total weight is proper: if a
    coalition's weight meets the quota, the complementary coalition's weight is strictly below it
    (the two complementary weights sum to the total, which is less than `2 * quota`), so the
    complement loses. No sign assumption on the weights is needed — this is a pure consequence of
    the quota-to-total ratio. -/
theorem weighted_voting_game_proper (weights : N → ℝ) (quota : ℝ) (hquota : 0 < quota)
    (hproper : 2 * quota > ∑ i, weights i) :
    ProperGame (WeightedVotingGame weights quota hquota) := by
  intro S hwin
  simp only [WeightedVotingGame] at hwin ⊢
  -- Decode `S` winning into its weight reaching the quota.
  have hS : ∑ i ∈ S, weights i ≥ quota := by
    split_ifs at hwin with h
    · exact h
    · linarith
  -- The complementary coalition's weight is `total − ∑_S`, hence `< quota`.
  have hSc : ∑ i ∈ Sᶜ, weights i = ∑ i, weights i - ∑ i ∈ S, weights i := by
    rw [← Finset.sum_add_sum_compl S weights]; ring
  have hSc_lt : ∑ i ∈ Sᶜ, weights i < quota := by rw [hSc]; linarith
  -- The complement does not reach the quota, so its value is `0`.
  split_ifs with h
  · linarith
  · rfl

/-! ## Self-dual games

A *self-dual* (transferable-utility) game is one that is simultaneously *proper* (a coalition and
its complement cannot both win) and *strong* (they cannot both lose). For a simple game this is
the canonical "decisive" / self-dual voting game: for every coalition, exactly one of it and its
complement wins. -/
def SelfDualGame (G : TUGame N) : Prop :=
  ProperGame G ∧ StrongGame G

namespace SelfDualGame

/-- A self-dual game is proper. -/
theorem proper (G : TUGame N) (hG : SelfDualGame G) : ProperGame G := hG.1

/-- A self-dual game is strong. -/
theorem strong (G : TUGame N) (hG : SelfDualGame G) : StrongGame G := hG.2

/-- In a self-dual simple game, exactly one of a coalition and its complement wins: `v S = 1`
    forces `v Sᶜ = 0` (proper), and `v S = 0` forces `v Sᶜ = 1` (strong). -/
theorem complement_flip {G : TUGame N} (hG : SelfDualGame G) {S : Finset N}
    (hS : G.v S = 1 ∨ G.v S = 0) : G.v Sᶜ = 0 ∨ G.v Sᶜ = 1 := by
  rcases hS with h1 | h0
  · exact Or.inl (hG.1 h1)
  · exact Or.inr (hG.2 h0)

end SelfDualGame

/-- Player i is critical in coalition S if removing them causes S to lose -/
def Critical (G : TUGame N) (i : N) (S : Finset N) : Prop :=
  i ∈ S ∧ G.v S = 1 ∧ G.v (S.erase i) = 0

/-- A critical player must be a member of the coalition: `Critical G i S` unfolds to
    `i ∈ S ∧ …`, so membership is the first conjunct. Warm-up BG-prover target (#1453):
    trivial conjunct extraction, exercises the harness on a second real target now that
    the bullet-sorry stub format fixes GoalExtract (cycle 63). -/
theorem critical_implies_mem (G : TUGame N) (i : N) (S : Finset N) :
    Critical G i S → i ∈ S := by
  intro h
  exact h.1

/-- `Critical G i` is decidable via Classical reasoning (the `TUGame.v` comparisons are
    noncomputable reals). Promoted to a global instance so that `BanzhafRaw` and any
    theorem about it synthesise the SAME instance, avoiding the
    opaque-`Classical.decPred`-mismatch trap. -/
noncomputable instance criticalDecidable (G : TUGame N) (i : N) :
    DecidablePred (fun S : Finset N => Critical G i S) := Classical.decPred _

/-- Raw Banzhaf index: number of coalitions where i is critical. -/
noncomputable def BanzhafRaw (G : TUGame N) (i : N) : ℕ :=
  (Finset.univ.filter fun S => Critical G i S).card

/-- `BanzhafRaw G i` is bounded by the total number of coalitions (`2^|N|`):
the critical coalitions are a subset of `Finset.univ`. First genuinely-provable,
non-smoke target for the BG prover (#1453). -/
theorem banzhaf_raw_le_univ (G : TUGame N) (i : N) :
    BanzhafRaw G i ≤ (Finset.univ : Finset (Finset N)).card := by
  unfold BanzhafRaw
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Player with veto power -/
def VetoPlayer (G : TUGame N) (i : N) : Prop :=
  ∀ S : Finset N, G.v S = 1 → i ∈ S

/-- Dictator: can win alone and has veto -/
def Dictator (G : TUGame N) (i : N) : Prop :=
  G.v {i} = 1 ∧ VetoPlayer G i

/-- A game has at most one dictator.

    If both `i` and `j` are dictators, then `j` is a veto player (`Dictator` second conjunct),
    and `i` wins alone (`v {i} = 1`, first conjunct of `Dictator i`). Applying the veto
    property of `j` to the winning coalition `{i}` forces `j ∈ {i}`, i.e. `j = i`. -/
theorem dictator_unique (G : TUGame N) (i j : N) (hi : Dictator G i) (hj : Dictator G j) :
    i = j := by
  -- `j` is a veto player (`Dictator` second conjunct) and `i` wins alone
  -- (`v {i} = 1`, first conjunct), so the veto property forces `j ∈ {i}`, i.e. `j = i`.
  exact (Finset.mem_singleton.mp (hj.2 {i} hi.1)).symm

/-- A dictator has a strictly positive raw Banzhaf index. The positive counterpart of
    `dummy_banzhaf_raw_zero`: a dummy never changes a coalition's value (BanzhafRaw = 0),
    whereas a dictator wins alone (`v {i} = 1`, the first conjunct of `Dictator`) and the
    empty coalition has value `0` (`TUGame.empty_zero`), so `{i}` is a critical coalition
    (`i ∈ {i}`, `v {i} = 1`, `v ({i}.erase i) = v ∅ = 0`). Hence the critical-coalition
    filter is non-empty and its cardinality is positive. -/
theorem dictator_banzhaf_pos (G : TUGame N) (i : N) (h : Dictator G i) :
    0 < BanzhafRaw G i := by
  have hcrit : Critical G i ({i} : Finset N) := by
    refine ⟨?_, ?_, ?_⟩
    · simp
    · exact h.1
    · have herase : ({i} : Finset N).erase i = ∅ := by simp
      rw [herase]
      exact G.empty_zero
  simp only [BanzhafRaw]
  exact Finset.card_pos.mpr ⟨{i}, Finset.mem_filter.2 ⟨Finset.mem_univ _, hcrit⟩⟩

/-- A veto player makes every coalition it does **not** belong to losing.

    The contrapositive of the veto property: `VetoPlayer G i` forces `i ∈ S` for every winning
    `S`, so `i ∉ S` rules out `v S = 1`; combined with `SimpleGame` (which forces `v S ∈ {0, 1}`)
    this leaves `v S = 0`. The losing-coalition companion of `veto_critical_of_winning`
    (where that result shows a veto player is critical in every *winning* coalition, this one
    shows every coalition *without* the veto player is losing). -/
theorem veto_losing_without {G : TUGame N} (hG : SimpleGame G) {i : N}
    (hv : VetoPlayer G i) {S : Finset N} (hni : i ∉ S) : G.v S = 0 := by
  apply SimpleGame.eq_zero_of_ne_one hG S
  intro hone
  exact absurd (hv S hone) hni

/-- A veto player is critical in the grand coalition, provided the grand coalition wins.

    `VetoPlayer G i` forces `i ∈ S` for every winning `S`. Applied to `S = univ.erase i`, if
    `v (univ.erase i) = 1` then `i ∈ univ.erase i`, contradicting `i ∉ univ.erase i`; hence
    `v (univ.erase i) ≠ 1`, and `SimpleGame` forces `v (univ.erase i) = 0`. Together with
    `v univ = 1` (`hwin`) and `i ∈ univ`, this makes `univ` a critical coalition for `i`. -/
theorem veto_critical_in_grand {G : TUGame N} (hG : SimpleGame G) {i : N}
    (hv : VetoPlayer G i) (hwin : G.v Finset.univ = 1) :
    Critical G i Finset.univ := by
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.mem_univ i
  · exact hwin
  · apply SimpleGame.eq_zero_of_ne_one hG (Finset.univ.erase i)
    intro heq
    have hni : i ∉ Finset.univ.erase i := by simp [Finset.mem_erase]
    exact hni (hv (Finset.univ.erase i) heq)

/-- A veto player is critical in *every* winning coalition.

    The general form of which `veto_critical_in_grand` is the grand-coalition instance:
    specializing `S` to `Finset.univ` recovers it. `VetoPlayer G i` forces `i ∈ S` for every
    winning `S`. To show `i` is critical in a winning `S` we need `v (S.erase i) = 0`: if
    `v (S.erase i) = 1` then the veto property would force `i ∈ S.erase i`, contradicting
    `i ∉ S.erase i`; hence `v (S.erase i) ≠ 1`, and `SimpleGame` forces `v (S.erase i) = 0`.
    Together with `v S = 1` (`hwin`) and `i ∈ S`, this makes `S` a critical coalition for `i`. -/
theorem veto_critical_of_winning {G : TUGame N} (hG : SimpleGame G) {i : N}
    (hv : VetoPlayer G i) {S : Finset N} (hwin : G.v S = 1) :
    Critical G i S := by
  refine ⟨?_, ?_, ?_⟩
  · exact hv S hwin
  · exact hwin
  · apply SimpleGame.eq_zero_of_ne_one hG (S.erase i)
    intro heq
    have hni : i ∉ S.erase i := by simp [Finset.mem_erase]
    exact hni (hv (S.erase i) heq)

/-- A player is a veto player if and only if it is critical in every winning coalition.

    The reciprocal of `veto_critical_of_winning`: being a veto player is *equivalent* to being
    critical in every winning coalition. The forward direction is `veto_critical_of_winning` (a
    veto player belongs to every winning coalition and its removal makes it losing); the reverse
    direction is immediate because criticality `Critical G i S` includes the membership `i ∈ S`,
    so being critical in every winning coalition recovers `VetoPlayer G i` (`∀ winning S, i ∈ S`).
    The characterization is meaningful under non-degeneracy (existence of at least one winning
    coalition); in the fully degenerate case (no winning coalition) both sides hold vacuously. -/
theorem veto_iff_critical_of_winning {G : TUGame N} (hG : SimpleGame G) (i : N) :
    VetoPlayer G i ↔ ∀ S : Finset N, G.v S = 1 → Critical G i S := by
  constructor
  · exact fun hv S hS => veto_critical_of_winning hG hv hS
  · intro h S hS
    exact (h S hS).1

/-- A veto player has a strictly positive raw Banzhaf index when the grand coalition wins.

    The veto pendant of `dummy_banzhaf_raw_zero` (a dummy has `BanzhafRaw = 0`): a veto player
    is critical in the grand coalition (`veto_critical_in_grand`, using `SimpleGame`), so the
    critical-coalition filter is non-empty and its cardinality is positive. Note that, unlike
    `dictator_banzhaf_pos`, this needs the grand-coalition-wins hypothesis `hwin`: without any
    winning coalition a player is vacuously a veto player yet has `BanzhafRaw = 0`. -/
theorem veto_banzhaf_raw_pos (G : TUGame N) (hG : SimpleGame G) (i : N)
    (hv : VetoPlayer G i) (hwin : G.v Finset.univ = 1) :
    0 < BanzhafRaw G i := by
  have hcrit : Critical G i Finset.univ := veto_critical_in_grand hG hv hwin
  simp only [BanzhafRaw]
  exact Finset.card_pos.mpr ⟨Finset.univ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hcrit⟩⟩

/-- Dummy player: adds no value -/
def DummyPlayer (G : TUGame N) (i : N) : Prop :=
  ∀ S : Finset N, i ∉ S → G.v (S ∪ {i}) = G.v S

/-- Dummy players have zero Shapley value -/
theorem dummy_shapley_zero (G : TUGame N) (i : N) (h : DummyPlayer G i) :
    shapleyValue G i = 0 :=
  ShapleyValue.shapley_null_player G i h

/-- Dummy players are critical in no coalition, hence have a zero raw Banzhaf index.

    A dummy player never changes a coalition's value, so it can never be the case that
    `v S = 1` while `v (S.erase i) = 0`: the dummy hypothesis forces `v S = v (S.erase i)`,
    contradicting criticality. -/
theorem dummy_banzhaf_raw_zero (G : TUGame N) (i : N) (h : DummyPlayer G i) :
    BanzhafRaw G i = 0 := by
  -- A dummy player is critical in no coalition: criticality demands `v S = 1` and
  -- `v (S.erase i) = 0`, but `DummyPlayer` gives `v S = v (S.erase i)`.
  have hneq : ∀ S, Critical G i S → False := by
    rintro S ⟨hmem, hone, hzero⟩
    have hni : i ∉ S.erase i := by simp [Finset.mem_erase]
    -- `S = (S.erase i) ∪ {i}` since `i ∈ S`.
    have hS_eq : S = (S.erase i) ∪ {i} := by
      ext j
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
      constructor
      · intro hj
        by_cases heq : j = i
        · exact Or.inr heq
        · exact Or.inl ⟨heq, hj⟩
      · rintro (⟨_, hj⟩ | hj)
        · exact hj
        · rw [hj]; exact hmem
    have hdummy := h (S.erase i) hni
    rw [← hS_eq] at hdummy
    rw [hdummy] at hone
    linarith
  -- `BanzhafRaw` = cardinality of the critical-coalition filter (instance now consistent
  -- via `criticalDecidable`); the filter is empty since `hneq` refutes every criticality.
  simp only [BanzhafRaw]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun S _ hcrit => hneq S hcrit

/-- A veto player is never a dummy player, provided the grand coalition wins.

    The veto pendant of `dictator_not_dummy`: the two roles are mutually exclusive. A dummy
    player never changes a coalition's value; applied to `Finset.univ.erase i` (which `i` is
    absent from), this gives `v (univ.erase i ∪ {i}) = v (univ.erase i)`, i.e.
    `v univ = v (univ.erase i)`. But a veto player forces `v (univ.erase i) = 0` (via
    `veto_losing_without`, since `i ∉ univ.erase i`), while the non-degeneracy hypothesis
    `hwin : v univ = 1` gives `v univ = 1`. The equality `1 = 0` is a contradiction. -/
theorem veto_not_dummy (G : TUGame N) (hG : SimpleGame G) (i : N) (hv : VetoPlayer G i)
    (hwin : G.v Finset.univ = 1) : ¬ DummyPlayer G i := by
  intro hd
  -- A dummy never changes a coalition's value; applied to `univ.erase i` (which excludes `i`):
  have hni : i ∉ Finset.univ.erase i := by simp [Finset.mem_erase]
  have hdummy := hd (Finset.univ.erase i) hni
  -- `univ.erase i ∪ {i} = univ` (the player's absence followed by addition recovers the universe).
  have huniv : Finset.univ.erase i ∪ ({i} : Finset N) = Finset.univ := by
    ext j; simp [Finset.mem_univ]
  rw [huniv] at hdummy
  -- A veto player forces `v (univ.erase i) = 0` (it is absent from that coalition).
  rw [veto_losing_without hG hv hni] at hdummy
  -- `hdummy : v univ = 0` contradicts `hwin : v univ = 1`.
  rw [hdummy] at hwin
  linarith

/-- A dictator is never a dummy player.

    The two extreme player roles are mutually exclusive. A dummy player adds no value to any
    coalition it is absent from; applied to the empty coalition this yields `v (∅ ∪ {i}) = v ∅`,
    i.e. `v {i} = 0` (via `TUGame.empty_zero`). But a dictator wins alone (`v {i} = 1`, the first
    conjunct of `Dictator`), a contradiction. This is the player-type analogue of the BanzhafRaw
    sign split (`dictator_banzhaf_pos` : `> 0`, `dummy_banzhaf_raw_zero` : `= 0`). -/
theorem dictator_not_dummy (G : TUGame N) (i : N) (h : Dictator G i) :
    ¬ DummyPlayer G i := by
  intro hd
  -- The dummy hypothesis at the empty coalition gives `v {i} = v ∅ = 0`.
  have hdummy : G.v ({i} : Finset N) = 0 := by
    have hni : (i : N) ∉ (∅ : Finset N) := by simp
    have heq := hd ∅ hni
    rw [Finset.empty_union, G.empty_zero] at heq
    exact heq
  linarith [h.1]

/-- Coalitional swap used by `banzhaf_raw_symmetric`. In a coalition `S`, replace the lone
    member of `{i, j}` by the other (if `S` contains exactly one of `i, j`); coalitions
    containing both or neither are fixed. It is an involution and preserves the game value
    whenever `i, j` are symmetric in `G`. -/
private def banzhafSwap (i j : N) (S : Finset N) : Finset N :=
  if i ∈ S ∧ j ∉ S then (S.erase i) ∪ {j}
  else if j ∈ S ∧ i ∉ S then (S.erase j) ∪ {i}
  else S

/-- **Symmetry of the raw Banzhaf index.**

    Symmetric (interchangeable) players are critical in equally many coalitions, hence
    have equal raw Banzhaf indices. This is the Banzhaf analog of `shapley_symmetric`: the
    symmetry axiom is shared by every reasonable power index (Banzhaf as much as Shapley),
    even though only the full four-axiom package characterizes Shapley uniquely.

    The bijection `banzhafSwap i j` swaps `i ↔ j` throughout each coalition. It is an
    involution, preserves the game value (by `SymmetricPlayers`, after a case split on
    `S ∩ {i, j}`), and exchanges "critical for `i`" with "critical for `j`" (membership
    swaps, value is invariant, and `(σ S) \\ {j} = σ (S \\ {i})`). The two
    critical-coalition filters are therefore in bijection, so their cardinalities — the raw
    Banzhaf indices — coincide. -/
theorem banzhaf_raw_symmetric (G : TUGame N) (i j : N)
    (h : Solution.SymmetricPlayers G i j) :
    BanzhafRaw G i = BanzhafRaw G j := by
  classical
  by_cases heq : i = j
  · subst heq; rfl
  -- The hypothesis is symmetric in `i, j`.
  have hsymm : Solution.SymmetricPlayers G j i := fun S hj hi => (h S hi hj).symm
  -- Identity `(S.erase k) ∪ {k} = S` for `k ∈ S`.
  have aux_readd (k : N) {S : Finset N} (hk : k ∈ S) : (S.erase k) ∪ {k} = S := by
    rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hk]
  -- Behavior of `banzhafSwap i j` in each of the four membership cases.
  have swap_both {S : Finset N} (hSi : i ∈ S) (hSj : j ∈ S) : banzhafSwap i j S = S := by
    simp only [banzhafSwap]
    rw [if_neg (fun H => H.2 hSj), if_neg (fun H => H.2 hSi)]
  have swap_neither {S : Finset N} (hni : i ∉ S) (hnj : j ∉ S) : banzhafSwap i j S = S := by
    simp only [banzhafSwap]
    rw [if_neg (fun H => hni H.1), if_neg (fun H => hnj H.1)]
  have swap_i_only {S : Finset N} (hSi : i ∈ S) (hnj : j ∉ S) :
      banzhafSwap i j S = (S.erase i) ∪ {j} := by
    simp only [banzhafSwap]; rw [if_pos ⟨hSi, hnj⟩]
  have swap_j_only {S : Finset N} (hni : i ∉ S) (hSj : j ∈ S) :
      banzhafSwap i j S = (S.erase j) ∪ {i} := by
    simp only [banzhafSwap]
    rw [if_neg (fun H => hni H.1), if_pos ⟨hSj, hni⟩]
  -- (1) Involution: `banzhafSwap i j (banzhafSwap i j S) = S`.
  have hinv : ∀ S : Finset N, banzhafSwap i j (banzhafSwap i j S) = S := by
    intro S
    by_cases hSi : i ∈ S <;> by_cases hSj : j ∈ S
    · rw [swap_both hSi hSj, swap_both hSi hSj]
    · -- i ∈ S, j ∉ S : σ S = (S.erase i) ∪ {j}, which has j ∈, i ∉.
      have hσ : banzhafSwap i j S = (S.erase i) ∪ {j} := swap_i_only hSi hSj
      rw [hσ]
      have hmem_j : j ∈ (S.erase i) ∪ ({j} : Finset N) :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      have hni_mem : i ∉ (S.erase i) ∪ ({j} : Finset N) := by
        rw [Finset.mem_union, Finset.mem_singleton]
        rintro (h | hij)
        · exact absurd h (Finset.notMem_erase i S)
        · exact absurd hij heq
      rw [swap_j_only hni_mem hmem_j]
      -- ((S.erase i) ∪ {j}).erase j ∪ {i} = S
      have hnj_erase : j ∉ S.erase i :=
        fun Hh => hSj (Finset.mem_of_mem_erase Hh)
      rw [Finset.erase_union_distrib, Finset.erase_singleton,
          Finset.erase_eq_self.mpr hnj_erase, Finset.union_empty, aux_readd i hSi]
    · -- i ∉ S, j ∈ S : symmetric to the previous case.
      have hσ : banzhafSwap i j S = (S.erase j) ∪ {i} := swap_j_only hSi hSj
      rw [hσ]
      have hmem_i : i ∈ (S.erase j) ∪ ({i} : Finset N) :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      have hnj_mem : j ∉ (S.erase j) ∪ ({i} : Finset N) := by
        rw [Finset.mem_union, Finset.mem_singleton]
        rintro (h | hji)
        · exact absurd h (Finset.notMem_erase j S)
        · exact heq hji.symm
      rw [swap_i_only hmem_i hnj_mem]
      have hni_erase : i ∉ S.erase j :=
        fun Hh => hSi (Finset.mem_of_mem_erase Hh)
      rw [Finset.erase_union_distrib, Finset.erase_singleton,
          Finset.erase_eq_self.mpr hni_erase, Finset.union_empty, aux_readd j hSj]
    · rw [swap_neither hSi hSj, swap_neither hSi hSj]
  -- (2) Value invariance: `G.v (banzhafSwap i j S) = G.v S`.
  have hval : ∀ S : Finset N, G.v (banzhafSwap i j S) = G.v S := by
    intro S
    by_cases hSi : i ∈ S <;> by_cases hSj : j ∈ S
    · -- both in: σ S = S.
      rw [swap_both hSi hSj]
    · -- i in, j out: σ S = (S.erase i) ∪ {j}; value equals v S by symmetry on S.erase i.
      have hσ : banzhafSwap i j S = (S.erase i) ∪ {j} := swap_i_only hSi hSj
      rw [hσ]
      have hjni : j ∉ S.erase i := fun Hh => hSj (Finset.mem_of_mem_erase Hh)
      have hT := h (S.erase i) (Finset.notMem_erase i S) hjni
      rw [aux_readd i hSi] at hT
      exact hT.symm
    · -- i out, j in: σ S = (S.erase j) ∪ {i}.
      have hσ : banzhafSwap i j S = (S.erase j) ∪ {i} := swap_j_only hSi hSj
      rw [hσ]
      have hini : i ∉ S.erase j := fun Hh => hSi (Finset.mem_of_mem_erase Hh)
      have hT := hsymm (S.erase j) (Finset.notMem_erase j S) hini
      rw [aux_readd j hSj] at hT
      exact hT.symm
    · rw [swap_neither hSi hSj]
  -- `hkey`: when both i, j are in S, symmetry on S \\ {i,j} equates the two erased values.
  have hkey : ∀ S : Finset N, i ∈ S → j ∈ S →
      G.v (S.erase j) = G.v (S.erase i) := by
    intro S hSi hSj
    -- Erasing i then j is the same as erasing j then i.
    have erase_erase_comm : (S.erase i).erase j = (S.erase j).erase i := by
      ext x
      simp only [Finset.mem_erase]
      tauto
    set T := (S.erase j).erase i
    have hTni : i ∉ T := Finset.notMem_erase i (S.erase j)
    have hTnj : j ∉ T := fun Hh => Finset.notMem_erase j S (Finset.mem_of_mem_erase Hh)
    have h1 : T ∪ ({i} : Finset N) = S.erase j :=
      aux_readd i (Finset.mem_erase.mpr ⟨heq, hSi⟩)
    have h2 : T ∪ ({j} : Finset N) = S.erase i := by
      rw [show T = (S.erase i).erase j from by rw [erase_erase_comm]]
      exact aux_readd j (Finset.mem_erase.mpr ⟨fun hj => heq hj.symm, hSj⟩)
    rw [← h1, ← h2]
    exact h T hTni hTnj
  -- Identity: erasing j from (S.erase i) ∪ {j} yields S.erase i.
  have aux_erase_lone (S : Finset N) (hnj : j ∉ S.erase i) :
      ((S.erase i) ∪ ({j} : Finset N)).erase j = S.erase i := by
    rw [Finset.erase_union_distrib, Finset.erase_singleton,
        Finset.erase_eq_self.mpr hnj, Finset.union_empty]
  -- (3) "Critical for i" ↔ "critical for j (after the swap)".
  have hiff : ∀ S : Finset N, Critical G i S ↔ Critical G j (banzhafSwap i j S) := by
    intro S
    by_cases hSi : i ∈ S <;> by_cases hSj : j ∈ S
    · -- both in: σ S = S; relate v(S.erase i) and v(S.erase j) via `hkey`.
      rw [swap_both hSi hSj]
      refine ⟨fun ⟨_, h1, h0⟩ => ⟨hSj, h1, by rw [hkey S hSi hSj]; exact h0⟩,
              fun ⟨_, h1, h0⟩ => ⟨hSi, h1, by rw [← hkey S hSi hSj]; exact h0⟩⟩
    · -- i in, j out: σ S = (S.erase i) ∪ {j}.
      have hσ : banzhafSwap i j S = (S.erase i) ∪ {j} := swap_i_only hSi hSj
      rw [hσ]
      have hnj_ei : j ∉ S.erase i := fun Hh => hSj (Finset.mem_of_mem_erase Hh)
      have hval' : G.v ((S.erase i) ∪ {j}) = G.v S := by
        rw [← hσ]; exact hval S
      refine ⟨fun ⟨_, h1, h0⟩ =>
                ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)),
                 hval'.trans h1,
                 by rw [aux_erase_lone S hnj_ei]; exact h0⟩,
              fun ⟨_, h1, h0⟩ =>
                ⟨hSi, hval'.symm.trans h1,
                 by rw [aux_erase_lone S hnj_ei] at h0; exact h0⟩⟩
    · -- i out, j in: σ S = (S.erase j) ∪ {i}. Both sides are false.
      have hσ : banzhafSwap i j S = (S.erase j) ∪ {i} := swap_j_only hSi hSj
      rw [hσ]
      -- j ∉ (S.erase j) ∪ {i} (j was erased, j ≠ i), so `Critical G j (σ S)` is false;
      -- `Critical G i S` is also false since i ∉ S.
      have hnjs : j ∉ (S.erase j) ∪ ({i} : Finset N) := by
        rw [Finset.mem_union, Finset.mem_singleton]
        rintro (h | hji)
        · exact absurd h (Finset.notMem_erase j S)
        · exact heq hji.symm
      exact ⟨fun Hh => absurd Hh.1 hSi, fun Hh => absurd Hh.1 hnjs⟩
    · -- neither: σ S = S; both sides are false (i, j ∉ S).
      rw [swap_neither hSi hSj]
      exact ⟨fun Hh => absurd Hh.1 hSi, fun Hh => absurd Hh.1 hSj⟩
  -- (4) The swap is an involution hence injective; the j-critical filter is exactly the
  -- image of the i-critical filter under the swap, so the two cards coincide.
  show BanzhafRaw G i = BanzhafRaw G j
  simp only [BanzhafRaw]
  have hσ_inj : Function.Injective (banzhafSwap i j) := by
    intros a b hab
    have h2 : banzhafSwap i j (banzhafSwap i j a) = banzhafSwap i j (banzhafSwap i j b) :=
      congr_arg (banzhafSwap i j) hab
    rw [hinv, hinv] at h2
    exact h2
  have himage : (Finset.univ.filter fun S => Critical G j S) =
      Finset.image (banzhafSwap i j) (Finset.univ.filter fun S => Critical G i S) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hT
      refine ⟨banzhafSwap i j T, ?_, hinv T⟩
      have key : Critical G j (banzhafSwap i j (banzhafSwap i j T)) := by
        rw [hinv T]; exact hT
      exact (hiff (banzhafSwap i j T)).mpr key
    · rintro ⟨S, hS, hseq⟩
      have hcj := (hiff S).mp hS
      rwa [hseq] at hcj
  have hcard : (Finset.image (banzhafSwap i j)
        (Finset.univ.filter fun S => Critical G i S)).card =
      (Finset.univ.filter fun S => Critical G i S).card :=
    Finset.card_image_of_injective _ hσ_inj
  rw [himage, hcard]

/-! ## Normalized Banzhaf index -/

/-- The normalized (absolute Penrose-Banzhaf) power index: the raw Banzhaf count divided
    by `2 ^ (n - 1)`, the number of coalitions that contain the player (each of the other
    `n - 1` players is independently in or out). Equivalently, the probability that `i` is
    pivotal when a coalition containing `i` is drawn uniformly at random. Normalization
    makes the index comparable across player sets of different sizes. -/
noncomputable def BanzhafIndex (G : TUGame N) (i : N) : ℝ :=
  (BanzhafRaw G i : ℝ) / (2 : ℝ) ^ (Fintype.card N - 1)

/-- **Symmetry of the normalized Banzhaf index.** Symmetric (interchangeable) players have
    equal normalized Banzhaf indices: they have equal raw counts (`banzhaf_raw_symmetric`)
    and share the same normalizing denominator. This mirrors `shapley_symmetric`: the
    symmetry axiom is shared by every reasonable power index. -/
theorem banzhaf_index_symmetric (G : TUGame N) (i j : N)
    (h : Solution.SymmetricPlayers G i j) :
    BanzhafIndex G i = BanzhafIndex G j := by
  simp only [BanzhafIndex]
  rw [banzhaf_raw_symmetric G i j h]

/-- A dummy player has a zero normalized Banzhaf index: it is pivotal in no coalition, so
    its raw count (and hence its normalized share) is zero. -/
theorem banzhaf_index_dummy_zero (G : TUGame N) (i : N)
    (h : DummyPlayer G i) : BanzhafIndex G i = 0 := by
  simp only [BanzhafIndex, dummy_banzhaf_raw_zero G i h, Nat.cast_zero, zero_div]

/-- The normalized Banzhaf index is non-negative: `BanzhafRaw` is a natural count
    (>= 0 when cast to ℝ) and the normalizing denominator `2 ^ (card N - 1) > 0`.
    Real BG-prover target (#1453, cycle 65), stacks on #4071 (BanzhafIndex def).
    Slightly harder than the warm-ups: needs `div_nonneg` plus a positivity
    argument on the denominator. -/
theorem banzhaf_index_nonneg (G : TUGame N) (i : N) : 0 ≤ BanzhafIndex G i := by
  simp only [BanzhafIndex]
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · exact pow_nonneg (by norm_num) _

/-- The normalized Banzhaf index is zero exactly when the raw Banzhaf index is
    zero: `BanzhafIndex = BanzhafRaw / 2^(card N - 1)` and the normalizing
    denominator `2 ^ (card N - 1)` is strictly positive (so division by it is
    faithful). This strengthens `banzhaf_index_dummy_zero` (one direction) into a
    clean structural characterization.
    BG-prover target (#1453, cycle 66, item 4); a `div_eq_zero_iff₀` iff proof. -/
theorem banzhaf_index_eq_zero_iff (G : TUGame N) (i : N) :
    BanzhafIndex G i = 0 ↔ BanzhafRaw G i = 0 := by
  simp [BanzhafIndex]

/-- The normalized Banzhaf index is positive exactly when the raw Banzhaf index is
    positive: the `>0` dual of `banzhaf_index_eq_zero_iff`. Together the two iff
    theorems give a faithful characterization — the normalizer `2 ^ (card N - 1)` is
    strictly positive, so positivity and zerohood are both preserved by the division.
    BG-prover target (#1453, cycle 67, item 5); a positivity iff. -/
theorem banzhaf_index_pos_iff (G : TUGame N) (i : N) :
    0 < BanzhafIndex G i ↔ 0 < BanzhafRaw G i := by
  simp only [BanzhafIndex]
  have hden : 0 < (2 : ℝ) ^ (Fintype.card N - 1) := pow_pos (by norm_num) _
  constructor
  · intro h
    have hnumreal : 0 < (BanzhafRaw G i : ℝ) := (div_pos_iff_of_pos_right hden).mp h
    exact_mod_cast hnumreal
  · intro h
    exact div_pos (by exact_mod_cast h) hden

/-- The normalized Banzhaf index is at most 2: `BanzhafRaw` counts critical
    coalitions, bounded by the total number of coalitions `2 ^ card N` (see
    `banzhaf_raw_le_univ`); normalizing by `2 ^ (card N - 1)` leaves a quotient
    of at most 2. The player `i : N` forces `0 < card N`, so the Nat-subtraction
    `card N - 1` does not underflow.
    BG-prover target (#1453, cycle 66, item 3); chains `banzhaf_raw_le_univ`. -/
theorem banzhaf_index_le_two (G : TUGame N) (i : N) : BanzhafIndex G i ≤ 2 := by
  have hn : 0 < Fintype.card N := Fintype.card_pos_iff.mpr ⟨i⟩
  have hdenom : 0 < (2 : ℝ) ^ (Fintype.card N - 1) := pow_pos (by norm_num) _
  rw [BanzhafIndex, div_le_iff₀ hdenom]
  have hcard : (Finset.univ : Finset (Finset N)).card = 2 ^ Fintype.card N := by
    rw [Finset.card_univ, Fintype.card_finset]
  have h2 : (2 : ℝ) ^ Fintype.card N = 2 * (2 : ℝ) ^ (Fintype.card N - 1) := by
    have hkey : Fintype.card N = Fintype.card N - 1 + 1 := by omega
    conv_lhs => rw [hkey, pow_add, pow_one]
    ring
  calc (BanzhafRaw G i : ℝ)
      ≤ ((Finset.univ : Finset (Finset N)).card : ℝ) := by exact_mod_cast banzhaf_raw_le_univ G i
    _ = (2 ^ Fintype.card N : ℝ) := by rw [hcard]; norm_cast
    _ = 2 * (2 : ℝ) ^ (Fintype.card N - 1) := by rw [h2]

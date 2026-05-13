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
    G = ∑_{T≠∅} SmulGame (mobiusCoeff G T) (unanimityGame T)
    Proof: G.v S = ∑_{T≠∅,T⊆S} a_T  (mobius_decomposition_axiom)
         = ∑_{T≠∅} a_T*(if T⊆S then 1 else 0)  (reindex via filter_filter + sum_filter)
         = ∑_{T≠∅} SmulGame a_T u_T .v S  (def SmulGame + unanimityGame) -/
private theorem game_eq_mobius_sum (G : TUGame N) :
    G = Solution.finsetSumGames
      (Finset.univ.filter Finset.Nonempty)
      (fun T => if hT : T.Nonempty then
        Solution.SmulGame (Mobius.mobiusCoeff G T) (TUGame.unanimityGame T hT)
      else Solution.zeroGame) := by
  ext S
  simp only [Solution.finsetSumGames]
  classical
  rw [Mobius.mobius_decomposition_axiom G S]
  sorry

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
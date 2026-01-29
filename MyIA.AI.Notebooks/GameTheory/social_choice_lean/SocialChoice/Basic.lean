/-
  Social Choice Theory - Basic Definitions
  =========================================

  Port of asouther4/lean-social-choice to Lean 4
  Original: https://github.com/asouther4/lean-social-choice

  Core definitions for social choice theory:
  - Strict preference (P) and indifference (I)
  - Preference orders and quasi-orders
  - Choice sets and maximal elements
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic

variable {σ : Type*} {ι : Type*}

/-! ## Finset Utility Lemmas -/

lemma exists_distinct_mem_of_ne_singleton {s : Finset σ} {a : σ}
    (hs₁ : s.Nonempty) (hs₂ : s ≠ {a}) : ∃ b ∈ s, b ≠ a := by
  by_contra h
  push_neg at h
  have : s ⊆ {a} := fun x hx => Finset.mem_singleton.mpr (h x hx)
  have : s = {a} := by
    apply Finset.Subset.antisymm this
    obtain ⟨x, hx⟩ := hs₁
    simp only [Finset.singleton_subset_iff]
    rwa [h x hx]
  exact hs₂ this

lemma exists_second_distinct_mem {s : Finset σ} {a : σ}
    (hs : 2 ≤ s.card) (ha : a ∈ s) : ∃ b ∈ s, b ≠ a := by
  have hne : s.Nonempty := Finset.card_pos.mp (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hs)
  have hns : s ≠ {a} := by
    intro heq
    rw [heq] at hs
    simp at hs
  exact exists_distinct_mem_of_ne_singleton hne hns

lemma exists_third_distinct_mem {s : Finset σ} {a b : σ}
    (hs : 2 < s.card) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ∃ c ∈ s, c ≠ a ∧ c ≠ b := by
  have h2 : 2 ≤ (s.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  have hb' : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  obtain ⟨c, hc, hcb⟩ := exists_second_distinct_mem h2 hb'
  exact ⟨c, Finset.mem_of_mem_erase hc, Finset.ne_of_mem_erase hc, hcb⟩

/-! ## Strict Preference and Indifference -/

/-- Strict preference: x is strictly preferred to y under R -/
def P (R : σ → σ → Prop) (x y : σ) : Prop := R x y ∧ ¬R y x

/-- Indifference: x and y are equally ranked under R -/
def I (R : σ → σ → Prop) (x y : σ) : Prop := R x y ∧ R y x

/-- Two orderings agree on a pair of alternatives -/
def same_order (R R' : σ → σ → Prop) (x y x' y' : σ) : Prop :=
  ((R x y ↔ R' x' y') ∧ (R y x ↔ R' y' x')) ∧
  (P R x y ↔ P R' x' y') ∧ (P R y x ↔ P R' y' x')

/-- Simplified same_order for strict preferences only -/
def same_order' (R R' : σ → σ → Prop) (x y x' y' : σ) : Prop :=
  (P R x y ↔ P R' x' y') ∧ (P R y x ↔ P R' y' x')

/-! ## Transitivity Lemmas -/

lemma I_trans {R : σ → σ → Prop} {x y z : σ}
    (htrans : Transitive R) (h1 : I R x y) (h2 : I R y z) : I R x z :=
  ⟨htrans h1.1 h2.1, htrans h2.2 h1.2⟩

lemma P_trans_I {R : σ → σ → Prop} {x y z : σ}
    (htrans : Transitive R) (h1 : P R x y) (h2 : I R y z) : P R x z :=
  ⟨htrans h1.1 h2.1, fun h => h1.2 (htrans h2.2 h)⟩

lemma I_trans_P {R : σ → σ → Prop} {x y z : σ}
    (htrans : Transitive R) (h1 : I R y z) (h2 : P R x y) : P R x z :=
  ⟨htrans h2.1 h1.1, fun h => h2.2 (htrans h h1.2)⟩

lemma P_trans {R : σ → σ → Prop} {x y z : σ}
    (htrans : Transitive R) (h1 : P R x y) (h2 : P R y z) : P R x z :=
  ⟨htrans h1.1 h2.1, fun h => h1.2 (htrans h2.2 h)⟩

lemma R_of_nP_total {R : σ → σ → Prop} {x y : σ}
    (htot : Total R) (h : ¬P R y x) : R x y := by
  cases htot x y with
  | inl hxy => exact hxy
  | inr hyx => by_contra hnxy; exact h ⟨hyx, hnxy⟩

lemma nP_of_reverseP {R : σ → σ → Prop} {x y : σ} (h : P R x y) : ¬P R y x :=
  fun h' => h.2 h'.1

lemma nP_of_nR {R : σ → σ → Prop} {x y : σ} (h : ¬R x y) : ¬P R x y :=
  fun hp => h hp.1

lemma false_of_P_self {R : σ → σ → Prop} {x : σ} (h : P R x x) : False :=
  h.2 h.1

/-! ## Choice Sets and Maximal Elements -/

/-- x is a maximal element of S under R: nothing in S is strictly better -/
def is_maximal_element (x : σ) (S : Finset σ) (R : σ → σ → Prop) : Prop :=
  ∀ y ∈ S, ¬P R y x

/-- x is a best element of S under R: x is at least as good as everything -/
def is_best_element (x : σ) (S : Finset σ) (R : σ → σ → Prop) : Prop :=
  ∀ y ∈ S, R x y

/-- The maximal set: all maximal elements of S -/
noncomputable def maximal_set (S : Finset σ) (R : σ → σ → Prop) : Finset σ :=
  S.filter (fun x => is_maximal_element x S R)

/-- The choice set: all best elements of S -/
noncomputable def choice_set (S : Finset σ) (R : σ → σ → Prop) : Finset σ :=
  S.filter (fun x => is_best_element x S R)

/-! ## Quasi-Order Structure -/

/-- A quasi-order is reflexive and transitive -/
structure QuasiOrder (α : Type*) where
  rel : α → α → Prop
  refl : Reflexive rel
  trans : Transitive rel

instance (α : Type*) : CoeFun (QuasiOrder α) (fun _ => α → α → Prop) :=
  ⟨fun r => r.rel⟩

/-! ## Preference Order Structure -/

/-- A preference order is reflexive, total, and transitive -/
structure PrefOrder (α : Type*) where
  rel : α → α → Prop
  refl : Reflexive rel
  total : Total rel
  trans : Transitive rel

instance (α : Type*) : CoeFun (PrefOrder α) (fun _ => α → α → Prop) :=
  ⟨fun r => r.rel⟩

/-! ## Compatibility -/

/-- Q₁ is a subrelation of Q₂ -/
def is_subrelation (Q₁ Q₂ : QuasiOrder σ) : Prop :=
  ∀ x y : σ, (Q₁ x y → Q₂ x y) ∧ ((Q₁ x y ∧ ¬Q₁ y x) → ¬Q₂ y x)

/-- Q is compatible with R: Q extends to R preserving strict preferences -/
def is_compatible (Q : QuasiOrder σ) (R : PrefOrder σ) : Prop :=
  ∀ x y : σ, (Q x y → R x y) ∧ ((Q x y ∧ ¬Q y x) → ¬R y x)

/-! ## Acyclicality -/

/-- R is acyclical if there are no strict preference cycles -/
def acyclical (R : σ → σ → Prop) : Prop :=
  ∀ x : σ, ¬Relation.TransGen (P R) x x

/-! ## Key Theorems -/

/-- Best elements are maximal -/
theorem best_is_maximal {x : σ} {S : Finset σ} {R : σ → σ → Prop}
    (hx : is_best_element x S R) : is_maximal_element x S R := by
  intro y hy hPyx
  exact hPyx.2 (hx y hy)

/-- Choice set is subset of maximal set -/
theorem choice_subset_maximal (S : Finset σ) (R : σ → σ → Prop) :
    choice_set S R ⊆ maximal_set S R := by
  intro x hx
  simp only [choice_set, maximal_set, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, best_is_maximal hx.2⟩

/-- For quasi-orders, choice and maximal sets coincide -/
theorem choice_eq_maximal_of_quasi {S : Finset σ} {Q : QuasiOrder σ}
    (hS : S.Nonempty) : choice_set S Q.rel = maximal_set S Q.rel := by
  apply Finset.Subset.antisymm (choice_subset_maximal S Q.rel)
  intro x hx
  simp only [maximal_set, choice_set, Finset.mem_filter] at hx ⊢
  constructor
  · exact hx.1
  · intro y hy
    by_contra hny
    have : P Q.rel y x := ⟨by
      cases Q.total y x with
      | inl h => exact h
      | inr h => exact absurd h hny, hny⟩
    exact hx.2 y hy this

end

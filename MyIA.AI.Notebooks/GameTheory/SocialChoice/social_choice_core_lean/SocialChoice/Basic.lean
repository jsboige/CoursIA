/-
  Théorie du choix social — Définitions fondamentales
  ====================================================

  Port de asouther4/lean-social-choice vers Lean 4
  Original : https://github.com/asouther4/lean-social-choice

  Définitions fondamentales de la théorie du choix social :
  - Préférence stricte (P) et indifférence (I)
  - Ordres de préférence et quasi-ordres
  - Ensembles de choix et éléments maximaux
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic

variable {σ : Type*} {ι : Type*} [DecidableEq σ]

/-! ## Lemmes utilitaires sur les Finset -/

lemma exists_distinct_mem_of_ne_singleton {s : Finset σ} {a : σ}
    (hs₁ : s.Nonempty) (hs₂ : s ≠ {a}) : ∃ b ∈ s, b ≠ a := by
  by_contra h
  push_neg at h
  have hsub : s ⊆ {a} := fun x hx => Finset.mem_singleton.mpr (h x hx)
  have : s = {a} := Finset.Subset.antisymm hsub (by
    obtain ⟨a', ha'⟩ := hs₁
    rw [Finset.singleton_subset_iff]
    rw [← h a' ha']
    exact ha')
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

/-! ## Préférence stricte et indifférence -/

/-- Préférence stricte : x est strictement préféré à y selon R -/
def P (R : σ → σ → Prop) (x y : σ) : Prop := R x y ∧ ¬R y x

/-- Indifférence : x et y sont classés à égalité selon R -/
def I (R : σ → σ → Prop) (x y : σ) : Prop := R x y ∧ R y x

/-- Deux ordres coïncident sur une paire d'alternatives -/
def same_order (R R' : σ → σ → Prop) (x y x' y' : σ) : Prop :=
  ((R x y ↔ R' x' y') ∧ (R y x ↔ R' y' x')) ∧
  (P R x y ↔ P R' x' y') ∧ (P R y x ↔ P R' y' x')

/-- Variante simplifiée de same_order pour les préférences strictes uniquement -/
def same_order' (R R' : σ → σ → Prop) (x y x' y' : σ) : Prop :=
  (P R x y ↔ P R' x' y') ∧ (P R y x ↔ P R' y' x')

/-! ## Lemmes de transitivité -/

lemma I_trans {R : σ → σ → Prop} {x y z : σ}
    (htrans : Transitive R) (h1 : I R x y) (h2 : I R y z) : I R x z :=
  ⟨htrans h1.1 h2.1, htrans h2.2 h1.2⟩

lemma P_trans_I {R : σ → σ → Prop} {x y z : σ}
    (htrans : Transitive R) (h1 : P R x y) (h2 : I R y z) : P R x z :=
  ⟨htrans h1.1 h2.1, fun h => h1.2 (htrans h2.1 h)⟩

lemma I_trans_P {R : σ → σ → Prop} {x y z : σ}
    (htrans : Transitive R) (h1 : I R y z) (h2 : P R x y) : P R x z :=
  ⟨htrans h2.1 h1.1, fun h => h2.2 (htrans h1.1 h)⟩

lemma P_trans {R : σ → σ → Prop} {x y z : σ}
    (htrans : Transitive R) (h1 : P R x y) (h2 : P R y z) : P R x z :=
  ⟨htrans h1.1 h2.1, fun h => h1.2 (htrans h2.1 h)⟩

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

/-! ## Équivalence same_order pour les ordres totaux -/

/-- Pour les ordres totaux, R x y ↔ ¬P R y x -/
lemma R_iff_nP_rev {R : σ → σ → Prop} {x y : σ} (hR : Total R) :
    R x y ↔ ¬P R y x :=
  ⟨fun h hp => hp.2 h, R_of_nP_total hR⟩

/-- Pour les ordres totaux, same_order et same_order' sont équivalents -/
lemma same_order_iff_same_order' {R R' : σ → σ → Prop} {x y : σ}
    (hR : Total R) (hR' : Total R') :
    same_order R R' x y x y ↔ same_order' R R' x y x y := by
  refine ⟨fun h => h.2, fun h => ?_⟩
  refine ⟨⟨⟨fun hxy => ?_, fun hxy => ?_⟩, ⟨fun hyx => ?_, fun hyx => ?_⟩⟩, h⟩
  · -- R x y → R' x y : via ¬P R y x → ¬P R' y x
    exact (R_iff_nP_rev hR').mpr (mt h.2.mpr ((R_iff_nP_rev hR).mp hxy))
  · -- R' x y → R x y
    exact (R_iff_nP_rev hR).mpr (mt h.2.mp ((R_iff_nP_rev hR').mp hxy))
  · -- R y x → R' y x : via ¬P R x y → ¬P R' x y
    exact (R_iff_nP_rev hR').mpr (mt h.1.mpr ((R_iff_nP_rev hR).mp hyx))
  · -- R' y x → R y x
    exact (R_iff_nP_rev hR).mpr (mt h.1.mp ((R_iff_nP_rev hR').mp hyx))

/-! ## Ensembles de choix et éléments maximaux -/

/-- x est un élément maximal de S selon R : aucun élément de S n'est strictement préféré -/
def is_maximal_element (x : σ) (S : Finset σ) (R : σ → σ → Prop) : Prop :=
  ∀ y ∈ S, ¬P R y x

/-- x est un meilleur élément de S selon R : x est au moins aussi bon que tout élément -/
def is_best_element (x : σ) (S : Finset σ) (R : σ → σ → Prop) : Prop :=
  ∀ y ∈ S, R x y

/-- L'ensemble maximal : tous les éléments maximaux de S -/
noncomputable def maximal_set (S : Finset σ) (R : σ → σ → Prop) : Finset σ :=
  haveI : DecidablePred (fun x => is_maximal_element x S R) := Classical.decPred _
  S.filter (fun x => is_maximal_element x S R)

/-- L'ensemble de choix : tous les meilleurs éléments de S -/
noncomputable def choice_set (S : Finset σ) (R : σ → σ → Prop) : Finset σ :=
  haveI : DecidablePred (fun x => is_best_element x S R) := Classical.decPred _
  S.filter (fun x => is_best_element x S R)

/-! ## Structure de quasi-ordre -/

/-- Un quasi-ordre est réflexif et transitif -/
structure QuasiOrder (α : Type*) where
  rel : α → α → Prop
  refl : Reflexive rel
  trans : Transitive rel

instance (α : Type*) : CoeFun (QuasiOrder α) (fun _ => α → α → Prop) :=
  ⟨fun r => r.rel⟩

/-! ## Structure d'ordre de préférence -/

/-- Un ordre de préférence est réflexif, total et transitif -/
structure PrefOrder (α : Type*) where
  rel : α → α → Prop
  refl : Reflexive rel
  total : Total rel
  trans : Transitive rel

instance (α : Type*) : CoeFun (PrefOrder α) (fun _ => α → α → Prop) :=
  ⟨fun r => r.rel⟩

/-! ## Compatibilité -/

/-- Q₁ est une sous-relation de Q₂ -/
def is_subrelation (Q₁ Q₂ : QuasiOrder σ) : Prop :=
  ∀ x y : σ, (Q₁ x y → Q₂ x y) ∧ ((Q₁ x y ∧ ¬Q₁ y x) → ¬Q₂ y x)

/-- Q est compatible avec R : Q s'étend à R en préservant les préférences strictes -/
def is_compatible (Q : QuasiOrder σ) (R : PrefOrder σ) : Prop :=
  ∀ x y : σ, (Q x y → R x y) ∧ ((Q x y ∧ ¬Q y x) → ¬R y x)

/-! ## Acyclicité -/

/-- R est acyclique s'il n'existe aucun cycle de préférences strictes -/
def acyclical (R : σ → σ → Prop) : Prop :=
  ∀ x : σ, ¬Relation.TransGen (P R) x x

/-! ## Théorèmes-clés -/

/-- Les meilleurs éléments sont maximaux -/
theorem best_is_maximal {x : σ} {S : Finset σ} {R : σ → σ → Prop}
    (hx : is_best_element x S R) : is_maximal_element x S R := by
  intro y hy hPyx
  exact hPyx.2 (hx y hy)

/-- L'ensemble de choix est un sous-ensemble de l'ensemble maximal -/
theorem choice_subset_maximal (S : Finset σ) (R : σ → σ → Prop) :
    choice_set S R ⊆ maximal_set S R := by
  intro x hx
  simp only [choice_set, maximal_set, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, best_is_maximal hx.2⟩

/-- Pour les quasi-ordres totaux (c.-à-d. les ordres de préférence), les ensembles de choix et maximaux coïncident -/
theorem choice_eq_maximal_of_quasi {S : Finset σ} {Q : QuasiOrder σ}
    (hS : S.Nonempty) (htot : Total Q.rel) :
    choice_set S Q.rel = maximal_set S Q.rel := by
  apply Finset.Subset.antisymm (choice_subset_maximal S Q.rel)
  intro x hx
  simp only [maximal_set, choice_set, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, fun y hy => R_of_nP_total htot (hx.2 y hy)⟩

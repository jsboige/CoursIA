/-
Copyright (c) 2019 Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
  Patrick Massot

Port of mathlib4/Archive/Sensitivity.lean to standalone Lake workspace.
-/
import Sensitivity.Operator
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.FinCases

/-!
# Huang's sensitivity theorem (main result)

This file proves the main theorem: in the hypercube of dimension n ≥ 1,
if one colors more than half the vertices then at least one vertex has
at least √n colored neighbors.
-/

namespace Sensitivity

noncomputable section

open Function LinearMap Module Module.DualBases Finset

local notation "√" => Real.sqrt

local notation "dim " X:70 => Module.rank ℝ { x // x ∈ X }

local notation "fdim" => finrank ℝ

local notation "Span" => Submodule.span ℝ

local notation "Card " X:70 => Finset.card (Set.toFinset X)

variable {m : ℕ}

/-!
### The main proof

In this section, in order to enforce that `n` is positive, we write it as
`m + 1` for some natural number `m`. -/


open Classical in
/-- If a subset `H` of `Q (m+1)` has cardinal at least `2^m + 1` then the
subspace of `V (m+1)` spanned by the corresponding basis vectors non-trivially
intersects the range of `g m`. -/
theorem exists_eigenvalue (H : Set (Q m.succ)) (hH : Card H ≥ 2 ^ m + 1) :
    ∃ y ∈ Span (e '' H) ⊓ range (g m), y ≠ 0 := by
  let W := Span (e '' H)
  let img := range (g m)
  suffices 0 < dim (W ⊓ img) by
    exact mod_cast exists_mem_ne_zero_of_rank_pos this
  have dim_le : dim (W ⊔ img) ≤ 2 ^ (m + 1 : Cardinal) := by
    convert ← Submodule.rank_le (W ⊔ img)
    rw [← Nat.cast_succ]
    apply dim_V
  have dim_add : dim (W ⊔ img) + dim (W ⊓ img) = dim W + 2 ^ m := by
    convert ← Submodule.rank_sup_add_rank_inf_eq W img
    rw [rank_range_of_injective (g m) g_injective]
    apply dim_V
  have dimW : dim W = Fintype.card H := by
    have li : LinearIndependent ℝ (H.restrict e) := by
      convert (dualBases_e_ε m.succ).basis.linearIndependent.comp _ Subtype.val_injective
      rw [(dualBases_e_ε _).coe_basis]
      rfl
    have hdW := rank_span li
    rw [Set.range_restrict] at hdW
    convert hdW
    rw [← (dualBases_e_ε _).coe_basis, Cardinal.mk_image_eq (dualBases_e_ε _).basis.injective,
      Cardinal.mk_fintype]
  rw [← finrank_eq_rank ℝ] at dim_le dim_add dimW ⊢
  rw [← finrank_eq_rank ℝ, ← finrank_eq_rank ℝ] at dim_add
  norm_cast at dim_le dim_add dimW ⊢
  rw [pow_succ'] at dim_le
  rw [Set.toFinset_card] at hH
  linarith

open Classical in
/-- **Huang sensitivity theorem** also known as the **Huang degree theorem** -/
theorem huang_degree_theorem (H : Set (Q m.succ)) (hH : Card H ≥ 2 ^ m + 1) :
    ∃ q, q ∈ H ∧ √(m + 1) ≤ Card H ∩ q.adjacent := by
  rcases exists_eigenvalue H hH with ⟨y, ⟨⟨y_mem_H, y_mem_g⟩, y_ne⟩⟩
  have coeffs_support : ((dualBases_e_ε m.succ).coeffs y).support ⊆ H.toFinset := by
    intro p p_in
    rw [Finsupp.mem_support_iff] at p_in
    rw [Set.mem_toFinset]
    exact (dualBases_e_ε _).mem_of_mem_span y_mem_H p p_in
  obtain ⟨q, H_max⟩ : ∃ q : Q m.succ, ∀ q' : Q m.succ, |(ε q' :) y| ≤ |ε q y| :=
    Finite.exists_max _
  have H_q_pos : 0 < |ε q y| := by
    contrapose! y_ne
    exact epsilon_total fun p => abs_nonpos_iff.mp (le_trans (H_max p) y_ne)
  refine ⟨q, (dualBases_e_ε _).mem_of_mem_span y_mem_H q (abs_pos.mp H_q_pos), ?_⟩
  let s := √(m + 1)
  suffices s * |ε q y| ≤ _ * |ε q y| from (mul_le_mul_iff_left₀ H_q_pos).mp ‹_›
  let coeffs := (dualBases_e_ε m.succ).coeffs
  calc
    s * |ε q y| = |ε q (s • y)| := by
      rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ = |ε q (f m.succ y)| := by rw [← f_image_g y (by simpa using y_mem_g)]
    _ = |ε q (f m.succ (lc _ (coeffs y)))| := by rw [(dualBases_e_ε _).lc_coeffs y]
    _ =
        |(coeffs y).sum fun (i : Q m.succ) (a : ℝ) =>
            a • (ε q ∘ f m.succ ∘ fun i : Q m.succ => e i) i| := by
      rw [lc_def, (f m.succ).map_finsupp_linearCombination, (ε q).map_finsupp_linearCombination,
           Finsupp.linearCombination_apply]
    _ ≤ ∑ p ∈ (coeffs y).support, |coeffs y p * (ε q <| f m.succ <| e p)| :=
      (norm_sum_le _ fun p => coeffs y p * _)
    _ = ∑ p ∈ (coeffs y).support, |coeffs y p| * ite (p ∈ q.adjacent) 1 0 := by
      simp only [abs_mul, f_matrix]
    _ = ∑ p ∈ (coeffs y).support with q.adjacent p, |coeffs y p| := by
      simp [sum_filter]; rfl
    _ ≤ ∑ p ∈ (coeffs y).support with q.adjacent p, |coeffs y q| := sum_le_sum fun p _ ↦ H_max p
    _ = Finset.card {p ∈ (coeffs y).support | q.adjacent p} * |coeffs y q| := by
      rw [sum_const, nsmul_eq_mul]
    _ = Finset.card ((coeffs y).support ∩ q.adjacent.toFinset) * |coeffs y q| := by
      congr with x; simp; rfl
    _ ≤ Finset.card (H ∩ q.adjacent).toFinset * |ε q y| := by
      refine (mul_le_mul_iff_left₀ H_q_pos).2 ?_
      norm_cast
      apply card_le_card
      rw [Set.toFinset_inter]
      convert inter_subset_inter_right coeffs_support

end

end Sensitivity

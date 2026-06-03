/-
Copyright (c) 2019 Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
  Patrick Massot

Port of mathlib4/Archive/Sensitivity.lean to standalone Lake workspace.
-/
import Sensitivity.VectorSpace

/-!
# Linear operators for Huang's sensitivity theorem

This file defines the linear operators `f` (Huang's matrix) and `g` (Knuth's matrix),
and proves key properties: f² = n·id, injectivity of g, and the image relation.
-/

namespace Sensitivity

noncomputable section

open Function LinearMap Module

local notation "√" => Real.sqrt

variable {n : ℕ}

/-! ### The linear map -/


/-- The linear operator $f_n$ corresponding to Huang's matrix $A_n$,
defined inductively as a ℝ-linear map from `V n` to `V n`. -/
noncomputable def f : ∀ n, V n →ₗ[ℝ] V n
  | 0 => 0
  | n + 1 =>
    LinearMap.prod (LinearMap.coprod (f n) LinearMap.id) (LinearMap.coprod LinearMap.id (-f n))

@[simp]
theorem f_zero : f 0 = 0 :=
  rfl

theorem f_succ_apply (v : V n.succ) : f n.succ v = (f n v.1 + v.2, v.1 - f n v.2) := by
  cases v
  rw [f]
  simp only [sub_eq_add_neg]
  exact rfl

set_option backward.isDefEq.respectTransparency false in
theorem f_squared (v : V n) : (f n) (f n v) = (n : ℝ) • v := by
  induction n with
  | zero => simp only [Nat.cast_zero, zero_smul, f_zero, zero_apply]
  | succ n IH =>
    cases v; rw [f_succ_apply, f_succ_apply]; simp [IH, add_smul (n : ℝ) 1, add_assoc]; abel

set_option backward.isDefEq.respectTransparency false in
open Classical in
theorem f_matrix (p q : Q n) : |ε q (f n (e p))| = if p ∈ q.adjacent then 1 else 0 := by
  induction n with
  | zero =>
    dsimp [f]
    simp [Q.not_adjacent_zero]
    rfl
  | succ n IH =>
    have ite_nonneg : ite (π q = π p) (1 : ℝ) 0 ≥ 0 := by split_ifs <;> norm_num
    dsimp only [e, ε, f, V]; rw [LinearMap.prod_apply]; dsimp; cases hp : p 0 <;> cases hq : q 0
    all_goals
      repeat rw [Bool.cond_true]
      repeat rw [Bool.cond_false]
      simp [hp, hq, IH, duality, abs_of_nonneg ite_nonneg, Q.adj_iff_proj_eq,
        Q.adj_iff_proj_adj]

/-- The linear operator $g_m$ corresponding to Knuth's matrix $B_m$. -/
noncomputable def g (m : ℕ) : V m →ₗ[ℝ] V m.succ :=
  LinearMap.prod (f m + √(m + 1) • LinearMap.id) LinearMap.id

variable {m : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem g_apply : ∀ v, g m v = (f m v + √(m + 1) • v, v) := by
  delta g; intro v; simp

set_option backward.isDefEq.respectTransparency false in
theorem g_injective : Injective (g m) := by
  rw [g]
  intro x₁ x₂ h
  simp only [V, LinearMap.prod_apply, LinearMap.id_apply, Prod.mk_inj, Function.prod_apply] at h
  exact h.right

set_option backward.isDefEq.respectTransparency false in
theorem f_image_g (w : V m.succ) (hv : ∃ v, g m v = w) : f m.succ w = √(m + 1) • w := by
  rcases hv with ⟨v, rfl⟩
  have : √(m + 1) * √(m + 1) = m + 1 := Real.mul_self_sqrt (mod_cast zero_le)
  rw [f_succ_apply, g_apply]
  simp [this, f_squared, smul_add, add_smul, smul_smul]
  abel

end

end Sensitivity

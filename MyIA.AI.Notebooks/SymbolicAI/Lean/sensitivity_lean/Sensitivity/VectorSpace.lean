/-
Copyright (c) 2019 Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
  Patrick Massot

Port of mathlib4/Archive/Sensitivity.lean to standalone Lake workspace.
-/
import Sensitivity.Hypercube
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Vector space for Huang's sensitivity theorem

This file defines the free vector space `V n` on vertices of the hypercube,
the basis `e`, the dual basis `ε`, and proves duality and dimension results.
-/

namespace Sensitivity

noncomputable section

open Function LinearMap Module Module.DualBases

local notation "√" => Real.sqrt

/-! ### The vector space -/


/-- The free vector space on vertices of a hypercube, defined inductively. -/
def V : ℕ → Type
  | 0 => ℝ
  | n + 1 => V n × V n

@[simp]
theorem V_zero : V 0 = ℝ := rfl

@[simp]
theorem V_succ {n : ℕ} : V (n + 1) = (V n × V n) := rfl

namespace V

@[ext]
theorem ext {n : ℕ} {p q : V n.succ} (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q := Prod.ext h₁ h₂

variable (n : ℕ)

instance : DecidableEq (V n) := by induction n <;> · dsimp only [V]; infer_instance

instance : AddCommGroup (V n) := by induction n <;> · dsimp only [V]; infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : Module ℝ (V n) := by induction n <;> · dsimp only [V]; infer_instance

end V

/-- The basis of `V` indexed by the hypercube, defined inductively. -/
noncomputable def e : ∀ {n}, Q n → V n
  | 0 => fun _ => (1 : ℝ)
  | Nat.succ _ => fun x => cond (x 0) (e (π x), 0) (0, e (π x))

@[simp]
theorem e_zero_apply (x : Q 0) : e x = (1 : ℝ) :=
  rfl

/-- The dual basis to `e`, defined inductively. -/
noncomputable def ε : ∀ {n : ℕ}, Q n → V n →ₗ[ℝ] ℝ
  | 0, _ => LinearMap.id
  | Nat.succ _, p =>
    cond (p 0) ((ε <| π p).comp <| LinearMap.fst _ _ _) ((ε <| π p).comp <| LinearMap.snd _ _ _)

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
open Classical in
theorem duality (p q : Q n) : ε p (e q) = if p = q then 1 else 0 := by
  induction n with
  | zero => simp [Subsingleton.elim (α := Q 0) p q, ε, e]
  | succ n IH =>
    dsimp [ε, e]
    cases hp : p 0 <;> cases hq : q 0
    all_goals
      simp only [Bool.cond_true, Bool.cond_false, LinearMap.fst_apply, LinearMap.snd_apply,
        LinearMap.comp_apply, IH]
      congr 1; simp [Q.succ_n_eq, hp, hq]

/-- Any vector in `V n` annihilated by all `ε p`'s is zero. -/
theorem epsilon_total {v : V n} (h : ∀ p : Q n, (ε p) v = 0) : v = 0 := by
  induction n with
  | zero => dsimp [ε] at h; exact h fun _ => true
  | succ n ih =>
    obtain ⟨v₁, v₂⟩ := v
    ext <;> change _ = (0 : V n) <;> simp only <;> apply ih <;> intro p <;>
      [let q : Q n.succ := fun i => if h : i = 0 then true else p (i.pred h);
      let q : Q n.succ := fun i => if h : i = 0 then false else p (i.pred h)]
    all_goals
      specialize h q
      first
      | rw [ε, show q 0 = true from rfl, Bool.cond_true] at h
      | rw [ε, show q 0 = false from rfl, Bool.cond_false] at h
      rwa [show p = π q by ext; simp [q, Fin.succ_ne_zero, π]]

open Module

open Classical in
/-- `e` and `ε` are dual families of vectors. -/
theorem dualBases_e_ε (n : ℕ) : DualBases (@e n) (@ε n) where
  eval_same := by simp [duality]
  eval_of_ne _ _ h := by simp [duality, h]
  total h := sub_eq_zero.mp <| epsilon_total fun i ↦ by
    simpa only [map_sub, sub_eq_zero] using h i

theorem dim_V : Module.rank ℝ (V n) = 2 ^ n := by
  have : Module.rank ℝ (V n) = (2 ^ n : ℕ) := by
    classical
    rw [rank_eq_card_basis (dualBases_e_ε _).basis, Q.card]
  assumption_mod_cast

open Classical in
instance : FiniteDimensional ℝ (V n) :=
  (dualBases_e_ε _).basis.finiteDimensional_of_finite

theorem finrank_V : finrank ℝ (V n) = 2 ^ n := by
  have := @dim_V n
  rw [← finrank_eq_rank] at this; assumption_mod_cast

end

end Sensitivity

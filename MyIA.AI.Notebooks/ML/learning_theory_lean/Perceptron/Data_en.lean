import Mathlib

/-!
# Perceptron data — real inner product space, points, labels

The Novikoff theorem (1962) is proved in an **abstract real inner product space** `V`
(the `(R/γ)²` bound is independent of the dimension). This file gathers the elementary
geometric facts about the norm and the inner product needed for the proof, in
particular the expansion `‖a + b‖² = ‖a‖² + 2·⟪a, b⟫ + ‖b‖²` which is the core of
Lemma B (growth of the weight vector's norm).

The data itself (sequence of points `xₖ`, labels `yₖ ∈ {±1}`, unit separator `u` of
margin `γ`, radius `R`) is modeled in `Perceptron.lean` by the `PerceptronRun`
structure.

English mirror of `Perceptron/Data.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): distinct FR + EN sibling
files in the same lake, both compile; namespace `Perceptron_en` (anti-collision with
the FR `Perceptron` namespace); non-docstring proof code unchanged (Lean tactic names
and Mathlib references stay in English regardless).
-/

open scoped InnerProductSpace

namespace Perceptron_en

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `‖x‖² = ⟪x, x⟫_ℝ` — the square of the norm coincides with the self-inner product. -/
theorem norm_sq_eq_inner_self (x : V) : ‖x‖ ^ 2 = ⟪x, x⟫_ℝ :=
  (real_inner_self_eq_norm_sq x).symm

/-- Expansion of the squared norm of a sum:
`‖a + b‖² = ‖a‖² + 2·⟪a, b⟫ + ‖b‖²`. Central identity of Novikoff's Lemma B. -/
theorem norm_add_sq_eq (a b : V) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, b⟫_ℝ + ‖b‖ ^ 2 := by
  rw [norm_sq_eq_inner_self (a + b), real_inner_add_add_self,
      ← norm_sq_eq_inner_self a, ← norm_sq_eq_inner_self b]

/-- A **label** is a real scalar whose square is `1` (i.e. `±1`). -/
abbrev IsLabel (y : ℝ) : Prop :=
  y ^ 2 = 1

/-- A labeled point: a vector `x ∈ V` together with its label `y ∈ {±1}`. -/
structure LabeledPoint where
  /-- The vector (point in the space). -/
  x : V
  /-- The label (`±1`). -/
  y : ℝ

end Perceptron_en

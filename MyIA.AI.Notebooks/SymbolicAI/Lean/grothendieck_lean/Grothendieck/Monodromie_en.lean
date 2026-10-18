/-
# Hommage Grothendieck — Monodromy: the first step of the punctured circle

Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Proof component of the distillation #19333-G.beta (issue #21308)

English sibling of `Grothendieck/Monodromie.lean` (i18n convention #4980):
docstrings and comments translated, statements and proofs byte-identical.

Monodromy — the transformation undergone by a fiber carried along a loop
around a singular point — is used four times in the Lean series without ever
being defined (measured 18/10/2026: Lean-22, Lean-28, Riemann200). This
module lays its first step, on the example computable end to end: the
covering `z ↦ z²` of the punctured complex plane.

The generator loop `t ↦ exp(2πi·t)` lifts from `1` to `t ↦ exp(πi·t)`, and
that lift ends at `-1`: the monodromy is the transposition `x ↦ -x` of the
fiber `{1, -1}`. Of order 2, its nontrivial eigenvalue `-1` is a root of
unity — exactly what Grothendieck's quasi-unipotence theorem (SGA 7, XII)
predicts, stated below as a documentary `Prop`: Mathlib does not formalize
it, and this module says honestly where the boundary lies.

The universal covering `exp : ℂ → ℂ*` (the punctured plane) is the setting:
`Complex.exp_ne_zero` guarantees we never leave `ℂ*`.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Grothendieck_en

/-! ## The fiber of `z ↦ z²` above `1` -/

/-- The fiber of `z ↦ z²` above `1`: exactly `{1, -1}`, the two complex
square roots of unity. This is the fiber that the monodromy will permute. -/
theorem fiber_sq_one (x : ℂ) : x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    have h2 : (x - 1) * (x + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Or.inl (by linear_combination h3)
    · exact Or.inr (by linear_combination h3)
  · rintro (rfl | rfl)
    · norm_num
    · norm_num

/-! ## The generator loop and its lift -/

/-- The generator loop of the circle: `γ t = exp(2πi·t)`.
This is the base loop of `π₁(ℂ*)` — the universal covering
`exp : ℂ → ℂ*` makes it the generator (each full turn of the circle
corresponds to adding `2πi` in the covering space). -/
noncomputable def generatorLoop (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- Start of the loop: `γ 0 = 1`. -/
@[simp]
theorem generatorLoop_zero : generatorLoop 0 = 1 := by
  simp [generatorLoop]

/-- Return of the loop: `γ 1 = 1` — it is indeed a loop. The proof splits
the full turn into two half-turns and applies `exp (πi) = -1` twice. -/
@[simp]
theorem generatorLoop_one : generatorLoop 1 = 1 := by
  have h2 : generatorLoop 1
      = Complex.exp (Real.pi * Complex.I + Real.pi * Complex.I) := by
    simp only [generatorLoop]
    congr 1
    push_cast
    ring
  rw [h2, Complex.exp_add, Complex.exp_pi_mul_I]
  norm_num

/-- The lift of the loop by the square root: `γ̃ t = exp(πi·t)`.
It starts at `1` and covers `γ` point by point — this is the continuous
transport of the fiber along the loop. -/
noncomputable def generatorLift (t : ℝ) : ℂ := Complex.exp (Real.pi * Complex.I * t)

/-- The lift covers the loop: `γ̃(t)² = γ(t)` for every `t`. -/
@[simp]
theorem lift_covers_loop (t : ℝ) : generatorLift t ^ 2 = generatorLoop t := by
  simp only [generatorLift, generatorLoop, pow_two]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Start of the lift: `γ̃ 0 = 1`. -/
@[simp]
theorem lift_zero : generatorLift 0 = 1 := by
  simp [generatorLift]

/-- **The endpoint of the lift: `γ̃ 1 = -1`.**
The whole monodromy is in this line: carried once around the circle, the
square root `1` becomes `-1` — the algebraic object comes back transformed
by the loop. -/
@[simp]
theorem lift_one : generatorLift 1 = -1 := by
  simp [generatorLift, Complex.exp_pi_mul_I]

/-! ## Monodromy as an action on the fiber -/

/-- The monodromy of `z ↦ z²` along the generator: the transposition
`x ↦ -x` of the fiber `{1, -1}`. This is the action the lift makes the
fiber undergo: `1` leaves and comes back as `-1` (`lift_one`). -/
def monodromySq (x : ℂ) : ℂ := -x

/-- The monodromy preserves the fiber: the image of a square root of `1`
is one as well. -/
theorem monodromySq_mem_fiber {x : ℂ} (h : x ^ 2 = 1) : monodromySq x ^ 2 = 1 := by
  unfold monodromySq
  rw [neg_sq]
  exact h

/-- The monodromy is an involution: of order exactly `2`. -/
@[simp]
theorem monodromySq_sq (x : ℂ) : monodromySq (monodromySq x) = x := by
  simp [monodromySq, neg_neg]

/-- **The monodromy theorem, computed**: the monodromy sends the starting
point of the lift to its endpoint — `1 ↦ -1`. -/
theorem monodromy_of_generator : monodromySq (generatorLift 0) = generatorLift 1 := by
  simp [monodromySq, lift_zero, lift_one]

/-! ## Quasi-unipotence: the theorem and its boundary -/

/-- The second power of the monodromy is the identity — after two turns,
the object comes back unchanged. An operator of which some power is
unipotent (here: trivially, the identity) is quasi-unipotent. -/
theorem monodromySq_pow_two_eq_id (x : ℂ) : monodromySq (monodromySq x) = x :=
  monodromySq_sq x

/-- The nontrivial eigenvalue of the monodromy (`-1`) is a root of unity:
`(-1)² = 1`. This is the "roots of unity" half of quasi-unipotence,
verified on the example. -/
theorem eigenvalue_neg_one_sq : (-1 : ℂ) ^ 2 = 1 := by
  norm_num

/-- **Documentary statement (not proved — beyond Mathlib).**
Grothendieck's quasi-unipotence theorem (SGA 7, lecture XII, theorem 1.1;
see also *Weil II*, Deligne 1980): the monodromy of a smooth family
parametrized by a punctured disc is quasi-unipotent — some power of the
transformation is unipotent, in other words all its eigenvalues are roots
of unity. This `Prop` records the statement for memory; Mathlib 4 does not
formalize it (no theory of parametrized smooth families nor of ℓ-adic
monodromy), and the present module verifies its conclusion on the
computable example `z ↦ z²` above. -/
def quasiUnipotenceSGA7 : Prop :=
  ∀ (F : Type) [AddCommGroup F] [Module ℂ F] (T : F →ₗ[ℂ] F),
    (∃ (n : ℕ), 0 < n ∧ ∀ v : F, T^[n] v = v) →
      ∀ μ : ℂ, (∃ v : F, v ≠ 0 ∧ T v = μ • v) → ∃ (r : ℕ), 0 < r ∧ μ ^ r = 1

end Grothendieck_en

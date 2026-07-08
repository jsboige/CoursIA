import Mathlib

/-!
# PacLearning.Data — PAC model: instance space, distribution, errors

The **PAC** framework (Valiant 1984, *A theory of the learnable*) for a finite
hypothesis class. We set up the probabilistic model over a finite instance type
`X`: a **distribution** (normalized weight function `D : X → ℝ`, `∑ D x = 1`,
`D ≥ 0`), a **target concept** `f : X → Bool` and a **hypothesis** `h : X → Bool`.

- **True error** `trueError D f h := ∑ x, if h x ≠ f x then D.weight x else 0` —
  the mass (under `D`) of the instances misclassified by `h` (vs the concept `f`).
- **Empirical error** `empError f h S` — the proportion of mistakes of `h` over a
  sample `S : Fin n → X`.

We deliberately avoid the `ℝ≥0∞` / `Measure` machinery: for a finite instance
type, the normalized weight function over `ℝ` is enough and keeps the model
readable. This is the discrete counterpart of `PMF.toMeasure`, adapted to the
pedagogy of the bound.

This first deliverable sets up the **model** and the **elementary properties** of
the errors (bounds `[0, 1]`, zero error when `h = f`). The **sample-complexity
bound** `pac_finite_class_bound` (Hoeffding on the empirical error + union bound
over the finite class ⟹ `m ≥ (1/ε)(ln|H| + ln(1/δ))`) is **iteration 2+** —
documented OPEN, not sorry-backed.

English mirror of `PacLearning/Data.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): distinct FR + EN sibling
files in the same lake, both compile; namespace `PacLearning_en` (anti-collision
with the FR `PacLearning` namespace); non-docstring proof code unchanged.
-/

namespace PacLearning_en

open Finset

variable {X : Type*} [Fintype X]

/-- A probability distribution on `X` (finite): a normalized weight function.
We avoid the `ℝ≥0∞` / `Measure` machinery to keep the model pedagogical over `ℝ`. -/
structure Distribution (X : Type*) [Fintype X] where
  /-- Weight of each instance. -/
  weight : X → ℝ
  /-- The weights are non-negative. -/
  nonneg : ∀ x, 0 ≤ weight x
  /-- The total mass is 1. -/
  sum_one : ∑ x, weight x = 1

/-- Hypotheses and the target concept are functions `X → Bool`
(binary labels `±1`). -/
abbrev Hypothesis (X : Type*) := X → Bool

variable (D : Distribution X) (f h : Hypothesis X)

/-- **True error** of `h` (vs concept `f`) under distribution `D`:
mass of the misclassified instances (`h x ≠ f x`). -/
def trueError : ℝ :=
  ∑ x, if h x ≠ f x then D.weight x else 0

variable {D f h}

/-- The true error is non-negative (a sum of non-negative weights and zeros). -/
theorem trueError_nonneg : 0 ≤ trueError D f h := by
  dsimp only [trueError]
  apply sum_nonneg
  intro x _
  by_cases hx : h x ≠ f x
  · rw [if_pos hx]; exact D.nonneg x
  · rw [if_neg hx]

/-- A hypothesis that coincides with the concept (`h = f`) has zero true error. -/
theorem trueError_self : trueError D f f = 0 := by
  dsimp only [trueError]
  simp

/-- The true error is at most `1` (the total mass of `D` is `1`). -/
theorem trueError_le_one : trueError D f h ≤ 1 := by
  dsimp only [trueError]
  calc (∑ x, if h x ≠ f x then D.weight x else 0)
      ≤ ∑ x, D.weight x := by
        apply sum_le_sum
        intro x _
        by_cases hx : h x ≠ f x
        · rw [if_pos hx]
        · rw [if_neg hx]; exact D.nonneg x
    _ = 1 := D.sum_one

/-- The true error of `h` (vs `f`) equals that of `f` (vs `h`): the
"misclassified" relation is symmetric. -/
theorem trueError_comm : trueError D f h = trueError D h f := by
  dsimp only [trueError]
  apply congr_arg
  ext x
  by_cases hx : h x ≠ f x
  · rw [if_pos hx, if_pos (ne_comm.mp hx)]
  · rw [if_neg hx, if_neg (fun h' => hx (ne_comm.mp h'))]

section Empirical

/-- **Empirical error** of `h` on the sample `S : Fin n → X`: proportion
of the `n` examples misclassified. -/
noncomputable def empError (f h : Hypothesis X) {n : ℕ} (S : Fin n → X) : ℝ :=
  (∑ i : Fin n, if h (S i) ≠ f (S i) then (1 : ℝ) else 0) / n

/-- The empirical error is non-negative (non-negative numerator, strictly positive
denominator). -/
theorem empError_nonneg (f h : Hypothesis X) {n : ℕ} (S : Fin n → X) (hn : 0 < n) :
    0 ≤ empError f h S := by
  dsimp only [empError]
  apply div_nonneg
  · apply sum_nonneg
    intro i _
    by_cases hi : h (S i) ≠ f (S i)
    · rw [if_pos hi]; norm_num
    · rw [if_neg hi]
  · exact_mod_cast hn.le

/-- A hypothesis that coincides with the concept (`h = f`) has zero empirical
error (all indicators are zero). -/
theorem empError_self (f : Hypothesis X) {n : ℕ} (S : Fin n → X) :
    empError f f S = 0 := by
  dsimp only [empError]; simp

/-- The empirical error is at most `1`: at worst all `n` instances are
misclassified, i.e. a ratio `n / n = 1`. -/
theorem empError_le_one (f h : Hypothesis X) {n : ℕ} (S : Fin n → X) (hn : 0 < n) :
    empError f h S ≤ 1 := by
  dsimp only [empError]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (∑ i : Fin n, if h (S i) ≠ f (S i) then (1:ℝ) else 0) ≤ (n : ℝ) := by
    calc (∑ i : Fin n, if h (S i) ≠ f (S i) then (1:ℝ) else 0)
        ≤ ∑ i : Fin n, (1:ℝ) := sum_le_sum fun i _ => by
          by_cases hi : h (S i) ≠ f (S i)
          · rw [if_pos hi]
          · rw [if_neg hi]; norm_num
      _ = (n : ℝ) := by simp
  -- (Σ/n ≤ 1) ⟺ (Σ ≤ 1*n = n) when n > 0.
  rw [div_le_iff₀ hnpos, one_mul]
  exact hsum

/-- The empirical error of `h` (vs `f`) equals that of `f` (vs `h`): the
"misclassified" relation is symmetric (equal indicators pointwise). -/
theorem empError_comm (f h : Hypothesis X) {n : ℕ} (S : Fin n → X) :
    empError f h S = empError h f S := by
  dsimp only [empError]
  have heq : (∑ i : Fin n, if h (S i) ≠ f (S i) then (1:ℝ) else 0) =
             (∑ i : Fin n, if f (S i) ≠ h (S i) then (1:ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : h (S i) ≠ f (S i)
    · rw [if_pos hi, if_pos (ne_comm.mp hi)]
    · rw [if_neg hi, if_neg (fun h' => hi (ne_comm.mp h'))]
  rw [heq]

end Empirical

end PacLearning_en

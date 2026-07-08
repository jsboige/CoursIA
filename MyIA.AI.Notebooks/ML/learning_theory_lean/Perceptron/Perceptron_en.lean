import Mathlib
import Perceptron.Data_en

/-!
# The perceptron and its execution — weight vector and valid runs

The perceptron update rule: upon a classification mistake on `(xₖ, yₖ)`, the weight
vector evolves by
```
w_{k+1} = wₖ + yₖ · xₖ        (w₀ = 0)
```
The sequence `perceptronWeights` encodes this evolution. A **valid run**
(`PerceptronRun`) records that we consider `n` consecutive updates, each being a
**mistake** (`yₖ · ⟨wₖ, xₖ⟩ ≤ 0`), on data of radius `R` separated by a unit vector
`u` with margin `γ`.

These two invariants (mistake + margin) are exactly what makes Novikoff's proof
work: the mistake caps the growth of `‖w‖`, the margin guarantees that of `⟨w, u⟩`.

English mirror of `Perceptron/Perceptron.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): distinct FR + EN sibling
files in the same lake, both compile; namespace `Perceptron_en` (anti-collision
with the FR `Perceptron` namespace); non-docstring proof code unchanged.
-/

open scoped InnerProductSpace

namespace Perceptron_en

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The sequence of perceptron weight vectors after `k` updates:
`w₀ = 0`, `w_{k+1} = wₖ + yₖ · xₖ`. -/
def perceptronWeights (pts : ℕ → V) (lbl : ℕ → ℝ) : ℕ → V
  | 0 => 0
  | k + 1 => perceptronWeights pts lbl k + lbl k • pts k

@[simp]
theorem perceptronWeights_zero (pts : ℕ → V) (lbl : ℕ → ℝ) :
    perceptronWeights pts lbl 0 = 0 :=
  rfl

theorem perceptronWeights_succ (pts : ℕ → V) (lbl : ℕ → ℝ) (k : ℕ) :
    perceptronWeights pts lbl (k + 1) =
      perceptronWeights pts lbl k + lbl k • pts k :=
  rfl

/-- A **valid perceptron run** on linearly separable data: `n` consecutive updates,
each being a mistake, on points of radius `R` separated by the unit vector `u` with
margin `γ`. -/
structure PerceptronRun (V : Type*) [SeminormedAddCommGroup V] [InnerProductSpace ℝ V] where
  /-- Number of updates (mistakes) considered. -/
  n : ℕ
  /-- The points `xₖ` (relevant for `k < n`). -/
  pts : ℕ → V
  /-- The labels `yₖ` (of square `1`, i.e. `±1`). -/
  lbl : ℕ → ℝ
  /-- Unit separator of margin `γ`. -/
  u : V
  /-- Data radius (`R ≥ 0`, `‖xₖ‖ ≤ R`). -/
  R : ℝ
  /-- Separation margin (`γ > 0`). -/
  γ : ℝ
  /-- The radius is non-negative. -/
  hR : 0 ≤ R
  /-- The margin is strictly positive. -/
  hγ : 0 < γ
  /-- The separator is unit. -/
  hUnit : ‖u‖ = 1
  /-- Each label is `±1`. -/
  hLbl : ∀ k < n, lbl k ^ 2 = 1
  /-- Each point has norm `≤ R`. -/
  hRad : ∀ k < n, ‖pts k‖ ≤ R
  /-- **Margin**: `γ ≤ yₖ · ⟨u, xₖ⟩` (the separator classifies correctly with margin). -/
  hMargin : ∀ k < n, γ ≤ lbl k * ⟪u, pts k⟫_ℝ
  /-- **Mistake**: `yₖ · ⟨wₖ, xₖ⟩ ≤ 0` (the k-th update is indeed a mistake). -/
  hMistake : ∀ k < n, lbl k * ⟪perceptronWeights pts lbl k, pts k⟫_ℝ ≤ 0

namespace PerceptronRun

/-- The weight vector before the `k`-th update. -/
abbrev w (run : PerceptronRun V) (k : ℕ) : V :=
  perceptronWeights run.pts run.lbl k

end PerceptronRun

end Perceptron_en

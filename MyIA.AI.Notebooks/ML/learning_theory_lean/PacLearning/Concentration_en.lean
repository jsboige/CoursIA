import Mathlib
import PacLearning.Data_en
import PacLearning.Sample_en

/-!
# PacLearning.Concentration — expectation and Markov inequality (ℝ-weight)

Submodule of `PacLearning`: **brick 2a/3** of iter-2. We define the **expectation**
of a function `g : X → ℝ` under distribution `D`, then the **Markov inequality**
in ℝ-weight. These two tools are the foundations of the Chernoff method
(Hoeffding-for-Bernoulli, brick 2b/3) and then of the `pac_finite_class_bound`
bound (brick 3/3).

We stay in the **pedagogical ℝ-weight style** of `Data.lean` / `Sample.lean`:
the expectation is the weighted sum `∑ x, D.weight x * g x`, without the
`ℝ≥0∞` / `Measure` / `Kernel` machinery of Mathlib. The Mathlib *lemmas* are reused
(`Finset.sum_*`, `log_le_sub_one_of_pos`, `convexOn_exp`) but not the *framework*
`HasSubgaussianMGF` + `iIndepFun` — disproportionate for the discrete model.

## Expectation and link to `trueError`

The true error `trueError D f h` can be reformulated as the expectation of the
misclassification indicator: `trueError D f h = expect D (fun x ↦ if h x ≠ f x then
1 else 0)`. This is the bridge between the model of `Data.lean` and the concentration
analysis.

English mirror of `PacLearning/Concentration.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): namespace
`PacLearning_en` (anti-collision with the FR `PacLearning` namespace); cross-module
`_en` imports `_en` (imports `PacLearning.Data_en` + `PacLearning.Sample_en`,
pattern Perceptron_en #5683 / Gittins_en); non-docstring proof code unchanged.
-/

namespace PacLearning_en

open Finset

variable {X : Type*} [Fintype X]
variable (D : Distribution X)

/-- **Expectation** of `g : X → ℝ` under distribution `D`: weighted sum.
This is the discrete counterpart of the integral `∫ g dD`. -/
noncomputable def expect (g : X → ℝ) : ℝ :=
  ∑ x, D.weight x * g x

variable {D}

/-- The expectation of a non-negative function is non-negative: a sum of
non-negative weights (`≥ 0`) times `g ≥ 0`. -/
theorem expect_nonneg {g : X → ℝ} (hg : ∀ x, 0 ≤ g x) : 0 ≤ expect D g := by
  dsimp only [expect]
  apply sum_nonneg
  intro x _
  exact mul_nonneg (D.nonneg x) (hg x)

/-- Expectation is linear in `g`: `E[a·g + b] = a·E[g] + b` (since `∑` is). -/
theorem expect_linear {g₁ g₂ : X → ℝ} (a b : ℝ) : expect D (fun x ↦ a * g₁ x + b * g₂ x) =
    a * expect D g₁ + b * expect D g₂ := by
  dsimp only [expect]
  simp only [mul_add, Finset.sum_add_distrib]
  -- Factor `a` (resp. `b`) moved to the left in each weighted scalar product,
  -- then `← mul_sum` pulls it out of the sum: `∑ (a·(w·g)) = a·∑ (w·g)`.
  simp only [show ∀ x, D.weight x * (a * g₁ x) = a * (D.weight x * g₁ x) from fun _ => by ring,
             show ∀ x, D.weight x * (b * g₂ x) = b * (D.weight x * g₂ x) from fun _ => by ring]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- The expectation of the constant function `c` is `c`: `∑ x, D.weight x * c = c`
(since the total mass is `1`). -/
theorem expect_const (c : ℝ) : expect D (fun _ ↦ c) = c := by
  dsimp only [expect]
  -- `∑ (w·c) = (∑ w)·c` (sum_mul inverted), then `∑ w = 1` and `1·c = c`.
  rw [← Finset.sum_mul, D.sum_one, one_mul]

/-- **Link to `trueError`**: the true error is the expectation of the
misclassification indicator `if h x ≠ f x then 1 else 0`. This is the bridge
between the model of `Data.lean` and the concentration analysis. -/
theorem trueError_eq_expect (f h : Hypothesis X) :
    trueError D f h = expect D (fun x ↦ if h x ≠ f x then (1 : ℝ) else 0) := by
  dsimp only [expect, trueError]
  apply sum_congr rfl
  intro x _
  by_cases hx : h x ≠ f x
  · simp only [if_pos hx, mul_one]
  · simp only [if_neg hx, mul_zero]

/-- **Markov inequality** (ℝ-weight): for `g ≥ 0` and `t > 0`,
`D-weight { x | t ≤ g x } ≤ E[g] / t`. Proof: on the filter `{x | t ≤ g x}`
(implemented as `Finset.filter` — membership via `Finset.mem_filter` is more
robust than the `Set`-comprehension `.toFinset` whose `Fintype ↑s` leaves a
universe metavariable) we have `t ≤ g` pointwise, hence `t · D.weight ≤
D.weight · g` (weight `≥ 0`), so `t · ∑_{filter} ≤ ∑_{filter} D.weight · g ≤
∑_{all} D.weight · g = E[g]`, and we divide by `t > 0`. -/
theorem markov_ineq {g : X → ℝ} (hg : ∀ x, 0 ≤ g x) {t : ℝ} (ht : 0 < t) :
    ∑ x ∈ Finset.filter (fun x => t ≤ g x) (Finset.univ : Finset X), D.weight x ≤
      expect D g / t := by
  dsimp only [expect]
  -- `le_div_iff₀` gives `(∑_F w) · t ≤ E[g]`, then `sum_mul` distributes the `t`.
  rw [le_div_iff₀ ht, Finset.sum_mul]
  -- Step 1: termwise `w·t ≤ w·g` on the filter (`t ≤ g`, `w ≥ 0`).
  have hF : ∑ x ∈ Finset.filter (fun x => t ≤ g x) Finset.univ, D.weight x * t ≤
            ∑ x ∈ Finset.filter (fun x => t ≤ g x) Finset.univ, D.weight x * g x := by
    apply sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 (D.nonneg x)
  -- Step 2: `∑_F w·t ≤ ∑_F w·g ≤ ∑_all w·g = E[g]`.
  calc ∑ x ∈ Finset.filter (fun x => t ≤ g x) Finset.univ, D.weight x * t
      ≤ ∑ x ∈ Finset.filter (fun x => t ≤ g x) Finset.univ, D.weight x * g x := hF
    _ ≤ ∑ x, D.weight x * g x :=
        sum_le_univ_sum_of_nonneg (fun x => mul_nonneg (D.nonneg x) (hg x))

end PacLearning_en

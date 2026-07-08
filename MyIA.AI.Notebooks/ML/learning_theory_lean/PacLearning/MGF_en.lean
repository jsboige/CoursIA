import Mathlib
import PacLearning.Data_en
import PacLearning.Sample_en
import PacLearning.Concentration_en

/-!
# PacLearning.MGF — moment generating function of the indicator (brick 2c/3-hoeffding-2a/5)

Submodule of `PacLearning`: analytic tool for Hoeffding concentration.
The Hoeffding chain for the mean of i.i.d. indicators rests on the
**moment generating function (MGF)** of the centered indicator:

    E_D [ exp (t · (ind(x) − μ)) ]   where  ind(x) = 𝟙{h(x) ≠ f(x)},  μ = trueError = E_D[ind].

This deliverable establishes the **algebraic reduction** (brick 2a/5): we reduce this
discrete MGF to a **closed form** depending only on `μ` and `t`:

    E_D [ exp (t · (ind − μ)) ] = μ · exp(t·(1−μ)) + (1−μ) · exp(−t·μ).

The idea: `ind(x) ∈ {0,1}`, so `exp(t·(ind−μ)) = exp(t(1−μ))·ind + exp(−tμ)·(1−ind)`
pointwise (if `ind = 1`, this reads `exp(t(1−μ))`; if `ind = 0`, `exp(−tμ)`). We then
distribute the expectation (`expect_linear`): `E[ind] = μ` (`trueError_eq_expect`),
`E[1 − ind] = 1 − μ` (`expect_sub` + `expect_const` + `D.sum_one`).

This is an **algebraic** ingredient (no analysis) preparing the **final bound**
`bernoulli_mgf_le : μ·exp(t(1−μ)) + (1−μ)·exp(−tμ) ≤ exp(t²/8)` (Hoeffding lemma,
brick 2b/5 — hard analytic core, dedicated cycle). We stay in the **pedagogical
ℝ-weight style**: the MGF is `expect D (fun x ↦ exp(t·(...)))`, a weighted sum over `D`.

English mirror of `PacLearning/MGF.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): namespace
`PacLearning_en` (anti-collision with the FR `PacLearning` namespace); cross-module
`_en` imports `_en` (imports `PacLearning.Data_en` + `PacLearning.Sample_en` +
`PacLearning.Concentration_en`, pattern Perceptron_en #5683 / Gittins_en);
non-docstring proof code unchanged.
-/

namespace PacLearning_en

open Finset
open scoped Classical

variable {X : Type*} [Fintype X]
variable (D : Distribution X)
variable {D}

/-- **Expectation of a pointwise difference**: `E_D[g − ind] = E_D[g] − E_D[ind]`
(weighted sum of differences = difference of weighted sums, via
`Finset.sum_sub_distrib`). Subtractive variant of `expect_linear`, reused by
`expect_exp_centered_eq` for `E_D[1 − ind] = 1 − trueError`. -/
theorem expect_sub (g₁ g₂ : X → ℝ) :
    expect D (fun x ↦ g₁ x - g₂ x) = expect D g₁ - expect D g₂ := by
  dsimp only [expect, expect]
  simp only [mul_sub]
  rw [← Finset.sum_sub_distrib]

/-- **Algebraic reduction of the MGF of the centered indicator**: for `ind(x) = 𝟙{h≠f}`
and `μ = trueError`, the moment generating function reduces to a closed form.

    E_D [ exp (t · (ind(x) − μ)) ] = μ · exp(t·(1−μ)) + (1−μ) · exp(−t·μ).

This is **brick 2a/5** of Hoeffding concentration: purely algebraic
(Fubini over the partition `{ind = 1}` / `{ind = 0}`), with no analysis. This is
the exact ingredient required by the final bound `bernoulli_mgf_le` (brick 2b/5, OPEN)
which will show this closed form is `≤ exp(t²/8)`.

Proof: pointwise, `exp(t·(ind−μ)) = exp(t(1−μ))·ind + exp(−tμ)·(1−ind)` (since
`ind ∈ {0,1}`: case `ind = 1` ⟹ `exp(t(1−μ))`; case `ind = 0` ⟹ `exp(−tμ)`). We then
distribute the expectation (`expect_linear`): `E[ind] = μ` (`trueError_eq_expect`) and
`E[1 − ind] = 1 − μ` (`expect_sub` + `expect_const`). -/
theorem expect_exp_centered_eq (f h : Hypothesis X) (t : ℝ) :
    expect D (fun x ↦ Real.exp (t * ((if h x ≠ f x then (1 : ℝ) else 0) - trueError D f h))) =
      trueError D f h * Real.exp (t * (1 - trueError D f h)) +
        (1 - trueError D f h) * Real.exp (-(t * trueError D f h)) := by
  set μ := trueError D f h
  -- (1) Pointwise identity: `exp(t·(ind−μ)) = exp(t(1−μ))·ind + exp(−tμ)·(1−ind)`,
  -- since `ind ∈ {0,1}` (the `exp(...)` constant on the LEFT so that `expect_linear` matches).
  -- The `exp` arguments are not defeq between branches (`t*(0−μ)` vs `−(t*μ)`), hence
  -- the final `congr 1; ring` to equalize the arguments under the exponential.
  have hind : ∀ x : X,
      Real.exp (t * ((if h x ≠ f x then (1 : ℝ) else 0) - μ)) =
        Real.exp (t * (1 - μ)) * (if h x ≠ f x then (1 : ℝ) else 0) +
          Real.exp (-(t * μ)) * (1 - (if h x ≠ f x then (1 : ℝ) else 0)) := by
    intro x
    by_cases hx : h x ≠ f x
    · -- `ind x = 1`: `exp(t(1−μ))·1 + exp(−tμ)·0 = exp(t(1−μ))`.
      simp only [if_pos hx, mul_one, mul_zero, sub_self, add_zero]
    · -- `ind x = 0`: `exp(t(0−μ)) = exp(t(1−μ))·0 + exp(−tμ)·(1−0) = exp(−tμ)`.
      -- simp reduces ifs + algebra; `Real.exp` is not handled by `ring`, hence the
      -- `congr 1` (peel exp) then `ring` on the argument `t*(0−μ) = −(t*μ)`.
      simp only [if_neg hx, mul_zero, mul_one, sub_zero, zero_add]
      congr 1
      ring
  -- (2) `E[ind] = μ` (the expectation of the indicator is the true error).
  have hind_exp : expect D (fun x ↦ if h x ≠ f x then (1 : ℝ) else 0) = μ :=
    (trueError_eq_expect (D := D) f h).symm
  -- (3) `E[1 − ind] = 1 − μ` (total mass `1` minus the error mass).
  have hcompl_exp : expect D (fun x ↦ 1 - (if h x ≠ f x then (1 : ℝ) else 0)) = 1 - μ := by
    rw [expect_sub, expect_const, hind_exp]
  -- (4) Assembly: pointwise identity (`congr`+`ext`), then `expect_linear`
  -- distributes each term in one go (constant on the left), then substitutions.
  calc expect D (fun x ↦ Real.exp (t * ((if h x ≠ f x then (1 : ℝ) else 0) - μ)))
      = expect D (fun x ↦
            Real.exp (t * (1 - μ)) * (if h x ≠ f x then (1 : ℝ) else 0) +
              Real.exp (-(t * μ)) * (1 - (if h x ≠ f x then (1 : ℝ) else 0))) := by
          congr 1; ext x; exact hind x
    _ = Real.exp (t * (1 - μ)) * expect D (fun x ↦ if h x ≠ f x then (1 : ℝ) else 0) +
          Real.exp (-(t * μ)) * expect D (fun x ↦ 1 - (if h x ≠ f x then (1 : ℝ) else 0)) := by
          rw [expect_linear]
    _ = Real.exp (t * (1 - μ)) * μ + Real.exp (-(t * μ)) * (1 - μ) := by
          rw [hind_exp, hcompl_exp]
    _ = μ * Real.exp (t * (1 - μ)) + (1 - μ) * Real.exp (-(t * μ)) := by
          rw [mul_comm (Real.exp (t * (1 - μ))) μ,
              mul_comm (Real.exp (-(t * μ))) (1 - μ)]

end PacLearning_en

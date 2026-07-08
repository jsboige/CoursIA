import Mathlib

/-!
# PacLearning.BernoulliMGF — analytic bound on the Bernoulli MGF (brick 2c/3-hoeffding-2b/5)

Submodule of `PacLearning`: the **analytic core** of Hoeffding concentration.
The previous brick (`MGF.lean`, PR #4525) algebraically reduced the centered MGF to
its closed form:

    E_D [ exp (t · (ind(x) − μ)) ] = μ · exp(t·(1−μ)) + (1−μ) · exp(−t·μ).

This brick (2b/5) bounds that closed form:

    μ · exp(t·(1−μ)) + (1−μ) · exp(−t·μ)  ≤  exp(t²/8)

for `μ ∈ [0, 1]` and `t ∈ ℝ`. This is **Hoeffding's lemma** (Bernoulli form) — the
hard analytic result required to close the concentration argument. We establish here
the **proven ingredients** (Bernoulli variance `≤ 1/4`, positivity, normalization, and
the **symmetric case `μ = 1/2`** via `cosh x ≤ exp(x²/2)`), and document the general
bound as OPEN with its variational proof sketch (Donsker–Varadhan + Pinsker).

## Why the general bound is OPEN (honest, G.3)

The bound `μ·exp(t(1−μ)) + (1−μ)·exp(−tμ) ≤ exp(t²/8)` is the real analytic content of
Hoeffding. Three proof routes, all heavy outside Mathlib's Measure framework:

1. **Second-deriv + Taylor**: `K(t) = ln(E[exp(t(ind−μ))])` satisfies `K(0) = K'(0) = 0`
   and `K''(t) ≤ 1/4` (variance of the **tilted** Bernoulli). Then `K(t) ≤ t²/8` via Taylor
   with integral remainder. Mathlib (`SubGaussian.lean:826`) follows this route but via
   `cgf` + `tilted` + `variance_le_sq_of_bounded` (Measure + ℝ≥0∞ framework).
2. **Variational (Donsker–Varadhan)**: `ln(p·e^a + (1−p)·e^b) = sup_q [q·a + (1−q)·b
   − D(q‖p)]` (KL). With `a = t(1−μ)`, `b = −tμ`: `K(t) = sup_q [t(q−μ) − D(q‖μ)]`.
   Pinsker `D(q‖μ) ≥ 2(q−μ)²` gives `K(t) ≤ sup_u [tu − 2u²] = t²/8`. The variational
   log-sum-exp lemma is absent from Mathlib outside `MeasureTheory/Measure/Tilted.lean`.
3. **2D optimization**: `h(μ,t) = exp(t²/8) − MGF ≥ 0` by critical-point analysis
   (non-trivial — the maximum of the MGF in `μ` is NOT at `1/2`).

The **symmetric case `μ = 1/2`** (this brick) closes elegantly: the MGF becomes
`cosh(t/2)` and `cosh x ≤ exp(x²/2)` (Mathlib `cosh_le_exp_half_sq`) gives
`cosh(t/2) ≤ exp((t/2)²/2) = exp(t²/8)`. The general bound is also closed here via a
derivative-monotonicity argument on the gap `g(t) = t²/8 − K(t)` (see
`bernoulli_mgf_le` below). This is dedicated analysis work; it is a real proof, not a
stub.

## Hoeffding bricks (decomposition into 5 sub-bricks)

- 1/5 Chernoff–Markov (`chernoff_ineq`) — PR #4516
- 2a/5 algebraic MGF reduction (`expect_exp_centered_eq`) — PR #4525
- **2b/5 analytic bound** — This module (ingredients + symmetric case proven, general
  bound proven via the gap method):
  - **2b/5-step2 DELIVERED**: the analytic core of Hoeffding proven — derivative of the
    log-MGF `φ'(t) = q(t)` (tilted mean), `q ∈ [0,1]`, and **2nd derivative
    `φ''(t) = q(t)(1−q(t)) ≤ 1/4`** (tilted variance, via the unconditional
    `bernoulli_var_le`). This is the exact ingredient of Hoeffding: the variance of a
    r.v. bounded in [0,1] is ≤ (range/2)² = 1/4.
  - **2b/5-final DELIVERED**: final bound `MGF ≤ exp(t²/8)` via the gap
    `g(t) = t²/8 − K(t) ≥ 0`, established by monotonicity of `g'` (no
    `convexOn_univ_of_deriv2_nonneg` / `deriv^[2]` machinery, which timeouts on `simp`).
- 3/5 product independence (MGF of a sum = product of MGFs) — OPEN
- 4/5 optimization `t = 4ε` — OPEN
- 5/5 two-sided concentration — OPEN

**Pedagogical ℝ-weight style** (no `ℝ≥0∞` / `Measure`), consistent with `Data.lean`.

EN mirror of `BernoulliMGF.lean` (EPIC #4980 i18n). Namespace `PacLearning_en` to avoid
collision with the FR canonical. Proof code unchanged; only docstrings/comments
translated FR→EN.
-/

namespace PacLearning_en

open Real

/-- **Bernoulli variance bound**: for all `μ ∈ ℝ`, `μ · (1 − μ) ≤ 1/4`. This is the key
fact underlying Hoeffding: the variance of a variable bounded in `[0, 1]` is bounded by
the square of the half-range `(1/2)²`. Proof: `1/4 − μ(1−μ) = (μ − 1/2)² ≥ 0`
(completing the square — so the bound is **unconditional**, true for every `μ`,
even outside `[0, 1]` where `μ(1−μ) < 0`). Exact ingredient of the bound `K''(t) ≤ 1/4`
(route 1 above). -/
theorem bernoulli_var_le (μ : ℝ) :
    μ * (1 - μ) ≤ 1 / 4 := by
  have h : 1 / 4 - μ * (1 - μ) = (μ - 1 / 2) ^ 2 := by ring
  linarith [sq_nonneg (μ - 1 / 2)]

/-- **Normalization**: the centered MGF equals `1` at `t = 0` (the exponential of `0` is
`1`, and `μ + (1 − μ) = 1`). This is `K(0) = ln(1) = 0`, the anchor point of the Taylor
route. -/
theorem bernoulli_mgf_zero (μ : ℝ) :
    μ * Real.exp (0 * (1 - μ)) + (1 - μ) * Real.exp (-(0 * μ)) = 1 := by
  simp only [zero_mul, Real.exp_zero, neg_zero]
  ring

/-- **Positivity (interior case)**: for `0 < μ < 1`, the centered MGF is strictly
positive (sum of two strictly positive terms: weight `> 0` times `exp > 0`). -/
theorem bernoulli_mgf_pos (μ t : ℝ) (hμ : 0 < μ) (hμ' : μ < 1) :
    0 < μ * Real.exp (t * (1 - μ)) + (1 - μ) * Real.exp (-(t * μ)) := by
  apply add_pos
  · exact mul_pos hμ (Real.exp_pos _)
  · exact mul_pos (by linarith) (Real.exp_pos _)

/-- **Hoeffding bound — symmetric case `μ = 1/2`**: the centered MGF at `μ = 1/2`
reduces to `cosh(t/2)`, and Mathlib's lemma `cosh x ≤ exp(x²/2)` gives the bound
`cosh(t/2) ≤ exp((t/2)²/2) = exp(t²/8)`.

This is the only case where the bound closes elegantly by symmetry (the MGF is symmetric
in `t`, the maximum in `μ` is reached at `1/2`). The general bound `μ·exp(t(1−μ)) +
(1−μ)·exp(−tμ) ≤ exp(t²/8)` for arbitrary `μ ∈ [0,1]` is proven by the gap method in
`bernoulli_mgf_le` below (the variational/Pinsker route or second-derivative route
remain heavy outside the Measure framework). -/
theorem bernoulli_mgf_half_le (t : ℝ) :
    (1 : ℝ) / 2 * Real.exp (t * ((1 : ℝ) / 2)) + (1 : ℝ) / 2 * Real.exp (-(t * ((1 : ℝ) / 2))) ≤
      Real.exp (t ^ 2 / 8) := by
  have hcosh : (1 : ℝ) / 2 * Real.exp (t * ((1 : ℝ) / 2)) + (1 : ℝ) / 2 * Real.exp (-(t * ((1 : ℝ) / 2))) =
      Real.cosh (t / 2) := by
    rw [Real.cosh_eq (t / 2)]
    field_simp
  rw [hcosh]
  have hle := Real.cosh_le_exp_half_sq (t / 2)
  rw [show (t / 2) ^ 2 / 2 = t ^ 2 / 8 from by ring] at hle
  exact hle

/-! ## Brick 2b/5-step2 — derivative of the log-MGF (tilted mean) and analytic bound

Analytic ingredient of the general bound `bernoulli_mgf_le` (proven below). We
establish the derivative structure of the **non-centered log-MGF** `φ(t) = log((1−μ) + μ·exp t)`:

  φ'(t) = q(t) := μ·exp t / ((1−μ) + μ·exp t)   ("tilted mean", ∈ [0,1] for μ ∈ [0,1])
  φ''(t) = q(t)·(1 − q(t)) ≤ 1/4                ("tilted variance", the exact Hoeffding ingredient)

The bound `φ'' ≤ 1/4` is the **analytic core** of Hoeffding (all the difficulty of the
concentration lives here: the variance of a r.v. bounded in [0,1] is ≤ (range/2)² = 1/4).
The final bound `MGF ≤ exp(t²/8)` follows by convexity/Taylor-style monotonicity
(`K(t) := φ(t) − tμ` has `K(0)=K'(0)=0` and `K'' = φ'' ≤ 1/4` ⟹ `K(t) ≤ t²/8`) —
proven via the gap method in `bernoulli_mgf_le`.
-/

/-- **Positivity of the log-MGF denominator**: for `μ ∈ [0,1]` and all `t`,
    `(1−μ) + μ·exp t > 0`. Indeed, it is a weighted sum (of `μ` and `1−μ`) of terms
    `≥ 0` of which at least one is strictly `> 0` (case `μ < 1`: `1−μ > 0`; case `μ = 1`:
    `μ·exp t = exp t > 0`). This is the domain condition of the log-MGF. -/
theorem bernoulli_logmgf_denom_pos (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    0 < (1 - μ) + μ * Real.exp t := by
  have h1mu : 0 ≤ 1 - μ := sub_nonneg.mpr hμ2
  have hmexp : 0 ≤ μ * Real.exp t := mul_nonneg hμ (le_of_lt (Real.exp_pos t))
  by_cases hμ1 : μ = 1
  · -- μ = 1: (1−μ) = 0, so the sum = 0 + exp t = exp t > 0.
    subst hμ1; simp [Real.exp_pos]
  · -- μ < 1: (1−μ) > 0, so the sum = (term ≥ 0) + (term > 0) > 0.
    have h1mu_pos : 0 < 1 - μ := lt_of_le_of_ne h1mu (fun heq => hμ1 (by linarith))
    linarith

/-- **Derivative of the Bernoulli log-MGF**: for `μ ∈ [0,1]` and the non-centered
    log-MGF `φ(t) = log((1−μ) + μ·exp t)`, the derivative is the "tilted mean"
    `q(t) = μ·exp t / ((1−μ) + μ·exp t)`. Proof: `HasDerivAt.log` (chain rule on `log`)
    + `hasDerivAt_exp` + `const_mul` + `const_add`, the denominator being `≠ 0`
    via `bernoulli_logmgf_denom_pos`. -/
theorem bernoulli_logmgf_deriv (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    deriv (fun s => Real.log ((1 - μ) + μ * Real.exp s)) t =
      μ * Real.exp t / ((1 - μ) + μ * Real.exp t) := by
  apply HasDerivAt.deriv
  apply HasDerivAt.log
  · exact HasDerivAt.const_add _ (HasDerivAt.const_mul _ (hasDerivAt_exp t))
  · exact ne_of_gt (bernoulli_logmgf_denom_pos μ t hμ hμ2)

/-- **The tilted mean lies in [0,1]**: for `μ ∈ [0,1]`, `q(t) = μ·exp t/((1−μ)+μ·exp t)
    ∈ [0,1]`. This is the "posterior probability" that `ind = 1` under the tilted law of
    parameter `t` — always a valid probability. -/
theorem bernoulli_tilted_mean_mem_Icc (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    μ * Real.exp t / ((1 - μ) + μ * Real.exp t) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  have hDpos : 0 < (1 - μ) + μ * Real.exp t := bernoulli_logmgf_denom_pos μ t hμ hμ2
  refine ⟨?_, ?_⟩
  · -- 0 ≤ μ·exp t / D  (numerator ≥ 0, denominator > 0).
    exact div_nonneg (mul_nonneg hμ (le_of_lt (Real.exp_pos t))) (le_of_lt hDpos)
  · -- μ·exp t / D ≤ 1  ⟺  μ·exp t ≤ (1−μ) + μ·exp t  ⟺  0 ≤ (1−μ)  (true since μ ≤ 1).
    rw [div_le_iff₀ hDpos, one_mul]
    exact le_add_of_nonneg_left (sub_nonneg.mpr hμ2)

/-- **Derivative of the tilted mean (= 2nd derivative of the log-MGF)**: for `q(t) =
    μ·exp t/((1−μ)+μ·exp t)` (the tilted mean, = `φ'`), we have `q'(t) = q(t)·(1−q(t))`
    (the "tilted variance"). This is the 2nd derivative `φ''(t)` of the non-centered
    log-MGF. Proof: quotient rule `HasDerivAt.div` on `num = μ·exp t` (numerator) and
    `D = (1−μ)+μ·exp t` (denominator, both with derivative `μ·exp t`), then algebraic
    closure (`field_simp` + `ring`): the quotient form `μ·exp t·(D − μ·exp t)/D²` reduces
    to `q(t)·(1−q(t))` because `D − μ·exp t = 1−μ`. -/
theorem bernoulli_tilted_mean_deriv (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    deriv (fun s => μ * Real.exp s / ((1 - μ) + μ * Real.exp s)) t =
      μ * Real.exp t / ((1 - μ) + μ * Real.exp t) *
        (1 - μ * Real.exp t / ((1 - μ) + μ * Real.exp t)) := by
  have hDpos : 0 < (1 - μ) + μ * Real.exp t := bernoulli_logmgf_denom_pos μ t hμ hμ2
  have hDne : (1 - μ) + μ * Real.exp t ≠ 0 := ne_of_gt hDpos
  have hnum : HasDerivAt (fun s => μ * Real.exp s) (μ * Real.exp t) t :=
    HasDerivAt.const_mul μ (hasDerivAt_exp t)
  have hD : HasDerivAt (fun s => (1 - μ) + μ * Real.exp s) (μ * Real.exp t) t :=
    HasDerivAt.const_add _ (HasDerivAt.const_mul _ (hasDerivAt_exp t))
  have hdiv : HasDerivAt (fun s => μ * Real.exp s / ((1 - μ) + μ * Real.exp s))
      ((μ * Real.exp t * ((1 - μ) + μ * Real.exp t) - μ * Real.exp t * (μ * Real.exp t)) /
        ((1 - μ) + μ * Real.exp t) ^ 2) t :=
    HasDerivAt.div hnum hD hDne
  rw [HasDerivAt.deriv hdiv]
  field_simp

/-- **The tilted variance is ≤ 1/4 (= the Hoeffding bound)**: the 2nd derivative of the
    non-centered log-MGF `φ''(t) = q(t)·(1−q(t))` satisfies `≤ 1/4` — the **analytic
    core** of Hoeffding. The bound `x·(1−x) ≤ 1/4` is **unconditional** (true ∀ `x ∈ ℝ`,
    via completing the square `(x − 1/2)² ≥ 0`), so it applies to `x = q(t)` with no
    domain hypothesis. This is the exact ingredient that, combined with the
    Taylor/convexity-style monotonicity on `K(t) = φ(t) − tμ` (with `K(0) = K'(0) = 0`),
    yields the final bound `MGF ≤ exp(t²/8)` (proven in `bernoulli_mgf_le`). -/
theorem bernoulli_logmgf_second_deriv_le (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    deriv (fun s => μ * Real.exp s / ((1 - μ) + μ * Real.exp s)) t ≤ 1 / 4 := by
  rw [bernoulli_tilted_mean_deriv μ t hμ hμ2]
  exact bernoulli_var_le _


/-! ## Brick 2b/5-final — general MGF bound `bernoulli_mgf_le`

The final Hoeffding bound (Bernoulli form): for `μ ∈ [0, 1]` and `t ∈ ℝ`,

    μ · exp(t · (1 − μ)) + (1 − μ) · exp(−(t · μ))  ≤  exp(t² / 8).

This is the complete **Hoeffding lemma**. The proof bypasses the heavy machinery
`convexOn_univ_of_deriv2_nonneg` + `deriv^[2]` (which timeouts on `simp`) by going
through **derivative monotonicity**: set the centered log-MGF
`K(t) = log((1−μ) + μ·exp t) − t·μ` (so that `MGF = exp(K)`), and the gap
`g(t) = t²/8 − K(t)`. We show `g ≥ 0` via:

1. the derivative `g'(t) = t/4 − (q(t) − μ)` (denoted `g₁`) is **globally monotone
   increasing** (`g₁'(t) = 1/4 − q(t)·(1−q(t)) ≥ 0` by `bernoulli_var_le`);
2. `g₁(0) = 0`, so `g₁(t) ≥ 0` for `t ≥ 0` (and `≤ 0` for `t ≤ 0`);
3. on `Set.Ici 0`, `g' = g₁ ≥ 0` ⟹ `g` monotone increasing ⟹ `g(t) ≥ g(0) = 0`;
4. on `Set.Iic 0`, `g' ≤ 0` ⟹ `g` monotone decreasing ⟹ `g(t) ≥ g(0) = 0`;
5. `g(t) ≥ 0` ⟹ `t²/8 ≥ K(t)` ⟹ (exp increasing) `exp(t²/8) ≥ exp(K(t)) = MGF`.

Monotonicity is established via `monotone_of_hasDerivAt_nonneg` /
`monotoneOn_of_deriv_nonneg` (pointwise HasDerivAt, **no `deriv^[2]`**, no global
`Differentiable ℝ` to synthesize).
-/

/-- The "tilted mean" `q(t) = μ·exp t / ((1−μ) + μ·exp t)`, exposed for reuse.
This is `φ'(t)` (derivative of the non-centered log-MGF) and the argument to
`bernoulli_var_le` giving `φ''(t) ≤ 1/4`. -/
noncomputable def bernoulliTiltedMean (μ t : ℝ) : ℝ := μ * Real.exp t / ((1 - μ) + μ * Real.exp t)

/-- `g₁ μ t = t/4 − (q(t) − μ)`: the derivative of the gap `g μ`. -/
noncomputable def bernoulliMGFDeriv (μ t : ℝ) : ℝ := t / 4 - (bernoulliTiltedMean μ t - μ)

/-- The gap `g μ t = t²/8 − K(t)` where `K(t) = log((1−μ)+μ·exp t) − t·μ` is the centered
log-MGF. Proving `g μ t ≥ 0` ⟹ `MGF ≤ exp(t²/8)`. -/
noncomputable def bernoulliMGFGap (μ t : ℝ) : ℝ := t^2 / 8 - (Real.log ((1 - μ) + μ * Real.exp t) - t * μ)

/-- `HasDerivAt` of the tilted mean: `q'(t) = q(t)·(1 − q(t))` (tilted variance). -/
theorem bernoulliTiltedMean_hasDerivAt (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    HasDerivAt (bernoulliTiltedMean μ)
      (bernoulliTiltedMean μ t * (1 - bernoulliTiltedMean μ t)) t := by
  have hDpos : 0 < (1 - μ) + μ * Real.exp t := bernoulli_logmgf_denom_pos μ t hμ hμ2
  have hDne : (1 - μ) + μ * Real.exp t ≠ 0 := ne_of_gt hDpos
  have hnum : HasDerivAt (fun s => μ * Real.exp s) (μ * Real.exp t) t :=
    HasDerivAt.const_mul μ (hasDerivAt_exp t)
  have hdenom : HasDerivAt (fun s => (1 - μ) + μ * Real.exp s) (μ * Real.exp t) t :=
    HasDerivAt.const_add _ (HasDerivAt.const_mul _ (hasDerivAt_exp t))
  have hdiv : HasDerivAt (fun s => μ * Real.exp s / ((1 - μ) + μ * Real.exp s))
      ((μ * Real.exp t * ((1 - μ) + μ * Real.exp t) - μ * Real.exp t * (μ * Real.exp t)) /
        ((1 - μ) + μ * Real.exp t) ^ 2) t :=
    HasDerivAt.div hnum hdenom hDne
  have hfun : (fun s => μ * Real.exp s / ((1 - μ) + μ * Real.exp s)) = bernoulliTiltedMean μ := by
    funext s; rfl
  rw [hfun] at hdiv
  have heq : bernoulliTiltedMean μ t * (1 - bernoulliTiltedMean μ t) =
      (μ * Real.exp t * ((1 - μ) + μ * Real.exp t) - μ * Real.exp t * (μ * Real.exp t)) /
        ((1 - μ) + μ * Real.exp t) ^ 2 := by
    simp only [bernoulliTiltedMean]
    field_simp
  rw [heq]
  exact hdiv

/-- `HasDerivAt` of the non-centered log-MGF `φ(t) = log((1−μ)+μ·exp t)`: `φ'(t) = q(t)`. -/
theorem bernoulli_logmgf_hasDerivAt (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    HasDerivAt (fun s => Real.log ((1 - μ) + μ * Real.exp s)) (bernoulliTiltedMean μ t) t := by
  have hDpos : 0 < (1 - μ) + μ * Real.exp t := bernoulli_logmgf_denom_pos μ t hμ hμ2
  have hDne : (1 - μ) + μ * Real.exp t ≠ 0 := ne_of_gt hDpos
  have hinner : HasDerivAt (fun s => (1 - μ) + μ * Real.exp s) (μ * Real.exp t) t :=
    HasDerivAt.const_add _ (HasDerivAt.const_mul _ (hasDerivAt_exp t))
  have hlog : HasDerivAt (fun s => Real.log ((1 - μ) + μ * Real.exp s))
      ((μ * Real.exp t) / ((1 - μ) + μ * Real.exp t)) t :=
    HasDerivAt.log hinner hDne
  simpa [bernoulliTiltedMean] using hlog

/-- `HasDerivAt` of the gap `g`: `g'(t) = g₁(t) = t/4 − (q(t) − μ)`. -/
theorem bernoulliMGFGap_hasDerivAt (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    HasDerivAt (bernoulliMGFGap μ) (bernoulliMGFDeriv μ t) t := by
  have hlog : HasDerivAt (fun s : ℝ => Real.log ((1 - μ) + μ * Real.exp s))
      (bernoulliTiltedMean μ t) t := bernoulli_logmgf_hasDerivAt μ t hμ hμ2
  have hsq8 : HasDerivAt (fun s : ℝ => s ^ 2 / 8) (2 * t / 8) t := by
    have h := HasDerivAt.div (hasDerivAt_pow 2 t) (hasDerivAt_const t 8) (by norm_num : (8 : ℝ) ≠ 0)
    convert h using 1 <;> first
      | rfl
      | (rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]; ring)
  have htmu : HasDerivAt (fun s : ℝ => s * μ) (1 * μ) t :=
    (hasDerivAt_id' t).mul_const μ
  have hK : HasDerivAt (fun s : ℝ => Real.log ((1 - μ) + μ * Real.exp s) - s * μ)
      (bernoulliTiltedMean μ t - 1 * μ) t := HasDerivAt.sub hlog htmu
  have hgap : HasDerivAt
      (fun s : ℝ => s ^ 2 / 8 - (Real.log ((1 - μ) + μ * Real.exp s) - s * μ))
      (2 * t / 8 - (bernoulliTiltedMean μ t - 1 * μ)) t :=
    HasDerivAt.sub hsq8 hK
  have hfun : (fun s : ℝ => s ^ 2 / 8 - (Real.log ((1 - μ) + μ * Real.exp s) - s * μ)) =
      bernoulliMGFGap μ := by funext s; rfl
  rw [hfun] at hgap
  have heq : bernoulliMGFDeriv μ t =
      2 * t / 8 - (bernoulliTiltedMean μ t - 1 * μ) := by
    simp only [bernoulliMGFDeriv, one_mul]
    ring
  rw [heq]
  exact hgap

/-- `g₁` is globally monotone increasing: `g₁'(t) = 1/4 − q(t)·(1−q(t)) ≥ 0` (bernoulli_var_le). -/
theorem bernoulliMGFDeriv_monotone (μ : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    Monotone (bernoulliMGFDeriv μ) := by
  apply monotone_of_hasDerivAt_nonneg
    (f' := fun x => 1 / 4 - bernoulliTiltedMean μ x * (1 - bernoulliTiltedMean μ x))
  · intro x
    have hs4 : HasDerivAt (fun s : ℝ => s / 4) (1 / 4) x := by
      have h := HasDerivAt.div (hasDerivAt_id' x) (hasDerivAt_const x 4) (by norm_num : (4 : ℝ) ≠ 0)
      convert h using 1 <;> first | rfl | ring
    have hq : HasDerivAt (bernoulliTiltedMean μ)
        (bernoulliTiltedMean μ x * (1 - bernoulliTiltedMean μ x)) x :=
      bernoulliTiltedMean_hasDerivAt μ x hμ hμ2
    have hqmu : HasDerivAt (fun s : ℝ => bernoulliTiltedMean μ s - μ)
        (bernoulliTiltedMean μ x * (1 - bernoulliTiltedMean μ x) - 0) x :=
      HasDerivAt.sub hq (hasDerivAt_const x μ)
    have hg1 : HasDerivAt (fun s : ℝ => s / 4 - (bernoulliTiltedMean μ s - μ))
        (1 / 4 - (bernoulliTiltedMean μ x * (1 - bernoulliTiltedMean μ x) - 0)) x :=
      HasDerivAt.sub hs4 hqmu
    have hfun : (fun s : ℝ => s / 4 - (bernoulliTiltedMean μ s - μ)) = bernoulliMGFDeriv μ := by
      funext s; rfl
    rw [hfun] at hg1
    convert hg1 using 1 <;> first | rfl | ring
  · intro x
    have h := bernoulli_var_le (bernoulliTiltedMean μ x)
    show 0 ≤ 1 / 4 - bernoulliTiltedMean μ x * (1 - bernoulliTiltedMean μ x)
    linarith

/-- `g₁(0) = 0` (since `q(0) = μ`). -/
theorem bernoulliMGFDeriv_zero (μ : ℝ) : bernoulliMGFDeriv μ 0 = 0 := by
  have hq : bernoulliTiltedMean μ 0 = μ := by
    simp only [bernoulliTiltedMean, Real.exp_zero, mul_one]
    field_simp
    ring
  simp only [bernoulliMGFDeriv, zero_div, hq, sub_self]

/-- `deriv g = g₁` (funext + HasDerivAt.deriv). -/
theorem deriv_bernoulliMGFGap (μ : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    deriv (bernoulliMGFGap μ) = bernoulliMGFDeriv μ := by
  funext x
  exact HasDerivAt.deriv (bernoulliMGFGap_hasDerivAt μ x hμ hμ2)

/-- `g` is continuous (composition of polynomial, log, exp; the log is defined since denom > 0). -/
theorem continuous_bernoulliMGFGap (μ : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    Continuous (bernoulliMGFGap μ) := by
  have hlog : Continuous (fun t : ℝ => Real.log ((1 - μ) + μ * Real.exp t)) := by
    apply Continuous.log
    · fun_prop
    · intro x; exact ne_of_gt (bernoulli_logmgf_denom_pos μ x hμ hμ2)
  show Continuous (fun t : ℝ => t ^ 2 / 8 - (Real.log ((1 - μ) + μ * Real.exp t) - t * μ))
  fun_prop

/-- `g(t) ≥ 0` for `0 ≤ t`: g monotone increasing on `Set.Ici 0`, `g(0) = 0`. -/
theorem bernoulliMGFGap_nonneg_of_nonneg (μ : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ bernoulliMGFGap μ t := by
  have hmono : MonotoneOn (bernoulliMGFGap μ) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_bernoulliMGFGap μ hμ hμ2).continuousOn
    · intro x _; exact (bernoulliMGFGap_hasDerivAt μ x hμ hμ2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [deriv_bernoulliMGFGap μ hμ hμ2]
      have h0x : (0 : ℝ) ≤ x := Set.mem_Ici.mp (interior_subset hx)
      have h1 : bernoulliMGFDeriv μ 0 ≤ bernoulliMGFDeriv μ x :=
        (bernoulliMGFDeriv_monotone μ hμ hμ2) h0x
      rw [bernoulliMGFDeriv_zero] at h1
      exact h1
  have h0 : bernoulliMGFGap μ 0 = 0 := by
    have h1 : (1 - μ : ℝ) + μ = 1 := by ring
    show (0 : ℝ) ^ 2 / 8 - (Real.log ((1 - μ) + μ * Real.exp 0) - 0 * μ) = 0
    simp only [Real.exp_zero, mul_one, zero_mul, sub_zero]
    rw [h1, Real.log_one]
    ring
  have hIn : (0 : ℝ) ∈ Set.Ici 0 := Set.mem_Ici.mpr (le_refl _)
  have htIn : t ∈ Set.Ici 0 := Set.mem_Ici.mpr ht
  have := hmono hIn htIn ht
  rwa [h0] at this

/-- `g(t) ≥ 0` for `t ≤ 0`: `−g` monotone increasing on `Set.Iic 0` (since `g' = g₁ ≤ 0` on
`Iio 0`), `g(0) = 0`. -/
theorem bernoulliMGFGap_nonneg_of_nonpos (μ : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) {t : ℝ}
    (ht : t ≤ 0) : 0 ≤ bernoulliMGFGap μ t := by
  have hcont : ContinuousOn (fun s => -bernoulliMGFGap μ s) (Set.Iic 0) :=
    (continuous_bernoulliMGFGap μ hμ hμ2).neg.continuousOn
  have hmono : MonotoneOn (fun s => -bernoulliMGFGap μ s) (Set.Iic 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
    · exact hcont
    · intro x _
      exact (bernoulliMGFGap_hasDerivAt μ x hμ hμ2).differentiableAt.neg.differentiableWithinAt
    · intro x hx
      have hderiv : deriv (fun s => -bernoulliMGFGap μ s) x = -bernoulliMGFDeriv μ x :=
        (bernoulliMGFGap_hasDerivAt μ x hμ hμ2).neg.deriv
      rw [hderiv]
      have hx0 : x ≤ (0 : ℝ) := Set.mem_Iic.mp (interior_subset hx)
      have h1 : bernoulliMGFDeriv μ x ≤ bernoulliMGFDeriv μ 0 :=
        (bernoulliMGFDeriv_monotone μ hμ hμ2) hx0
      rw [bernoulliMGFDeriv_zero] at h1
      linarith
  have h0 : bernoulliMGFGap μ 0 = 0 := by
    have h1 : (1 - μ : ℝ) + μ = 1 := by ring
    show (0 : ℝ) ^ 2 / 8 - (Real.log ((1 - μ) + μ * Real.exp 0) - 0 * μ) = 0
    simp only [Real.exp_zero, mul_one, zero_mul, sub_zero]
    rw [h1, Real.log_one]
    ring
  have hIn : (0 : ℝ) ∈ Set.Iic 0 := Set.mem_Iic.mpr (le_refl _)
  have htIn : t ∈ Set.Iic 0 := Set.mem_Iic.mpr ht
  have hle := hmono htIn hIn ht
  simp only at hle
  rw [h0, neg_zero] at hle
  linarith

/-- The **Hoeffding lemma** (Bernoulli form) — the final analytic bound. For `μ ∈ [0, 1]`
and all `t ∈ ℝ`, the centered MGF is bounded by `exp(t²/8)`. This is the exact ingredient
that, combined with product independence (brick 3/5) and the optimization `t = 4ε`
(brick 4/5), yields the two-sided Hoeffding concentration (brick 5/5). Proof via the gap
`g = t²/8 − log MGF ≥ 0` (derivative monotonicity, no `deriv^[2]`), then exponentiation. -/
theorem bernoulli_mgf_le (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    μ * Real.exp (t * (1 - μ)) + (1 - μ) * Real.exp (-(t * μ)) ≤ Real.exp (t ^ 2 / 8) := by
  have hgeq : 0 ≤ bernoulliMGFGap μ t := by
    by_cases ht : 0 ≤ t
    · exact bernoulliMGFGap_nonneg_of_nonneg μ hμ hμ2 ht
    · simp only [not_le] at ht
      exact bernoulliMGFGap_nonneg_of_nonpos μ hμ hμ2 ht.le
  have hDpos : 0 < (1 - μ) + μ * Real.exp t := bernoulli_logmgf_denom_pos μ t hμ hμ2
  have hlogle : Real.log ((1 - μ) + μ * Real.exp t) - t * μ ≤ t ^ 2 / 8 := by
    have heq : bernoulliMGFGap μ t = t ^ 2 / 8 - (Real.log ((1 - μ) + μ * Real.exp t) - t * μ) := rfl
    rw [heq, le_sub_iff_add_le] at hgeq
    linarith
  -- Product form (via `exp_add`, not `exp_sub`): the MGF = exp(log D) · exp(−tμ) = D · exp(−tμ).
  have hexp : (1 - μ + μ * Real.exp t) * Real.exp (-(t * μ)) ≤ Real.exp (t ^ 2 / 8) := by
    have hkey : Real.exp (Real.log ((1 - μ) + μ * Real.exp t) + -(t * μ)) ≤ Real.exp (t ^ 2 / 8) := by
      apply Real.exp_le_exp.mpr
      linarith [hlogle]
    rw [Real.exp_add, Real.exp_log hDpos] at hkey
    exact hkey
  -- Factorization: μ·exp(t(1−μ)) + (1−μ)·exp(−tμ) = (1−μ+μ·exp t)·exp(−tμ) (algebra, atoms
  -- `exp t` and `exp(−tμ)`), via `exp_add` on `exp(t(1−μ)) = exp(t − tμ)`.
  rw [show t * (1 - μ) = t + -(t * μ) by ring, Real.exp_add]
  have heq : μ * (Real.exp t * Real.exp (-(t * μ))) + (1 - μ) * Real.exp (-(t * μ)) =
      (1 - μ + μ * Real.exp t) * Real.exp (-(t * μ)) := by ring
  rw [heq]
  exact hexp


end PacLearning_en

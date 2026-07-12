import Mathlib
import PacLearning.Data_en
import PacLearning.Sample_en
import PacLearning.SampleExpect_en
import PacLearning.UnionBound_en
import PacLearning.MGF_en
import PacLearning.BernoulliMGF_en

/-!
# PacLearning_en.Hoeffding — Hoeffding-for-Bernoulli concentration (brick 2c/3, in progress)

EN mirror of `Hoeffding.lean` (EPIC #4980 i18n). Submodule of `PacLearning_en`: the
**analytic half** of the flagship `pac_finite_class_bound` (the other half, combinatorial
= union bound, is delivered in `UnionBound_en.lean`). We prove the **Hoeffding
concentration** for the mean of i.i.d. indicators:

    ℙ_S [ |empError − trueError| > ε ] ≤ 2·exp(−2·n·ε²).

Chernoff method (pedagogical ℝ-weight, not the Mathlib Kernel/Measure framework):

1. **Chernoff-Markov** (this deliverable, brick 1/5) — `ℙ[Y ≥ a] ≤ e^{−t·a}·E[e^{t·Y}]` for
   `t > 0`: Markov on the positive variable `Z = e^{t·Y}` at threshold `e^{t·a}`, via
   `{Z ≥ e^{t·a}} = {Y ≥ a}` (since `x ↦ e^{t·x}` is strictly increasing for `t > 0`).
2. **Bernoulli MGF** (OPEN, brick 2/5) — `E_D[exp(t·(ind − μ))] ≤ exp(t²/8)` (Hoeffding's
   lemma, `X ∈ [0,1]` ⟹ variance `≤ 1/4` ⟹ log-MGF `≤ t²/8`).
3. **Product independence** (OPEN, brick 3/5) — `E_S[exp(t·Σᵢ(ind(Sᵢ) − μ))] =
   ∏ᵢ E_D[...] ≤ exp(n·t²/8)` (`sampleExpect_coord` technique extended to products).
4. **Optimisation** (OPEN, brick 4/5) — `min_t e^{−t·n·ε}·e^{n·t²/8} = e^{−2·n·ε²}`
   (achieved at `t = 4ε`).
5. **Two-sided** (OPEN, brick 5/5) — `|empError − trueError| ≥ ε = (· ≥ ε) ∪ (· ≤ −ε)` →
   bound `· 2` via `sampleProb_union_bound` (UnionBound_en.lean).

This deliverable establishes **brick 1 (Chernoff-Markov)** `chernoff_ineq`, a fundamental
ingredient of the whole chain, fully proven (no deferral tactic). We stay in the
**pedagogical ℝ-weight** style: probability is a weighted sum (`sampleProb`), expectation
likewise (`sampleExpect`), and the Chernoff method appeals only to the monotonicity of
`sampleExpect` and to the growth of the exponential.

Namespace `PacLearning_en` to avoid collision with the FR canonical. Proof code unchanged;
only docstrings/comments translated FR→EN.
-/

namespace PacLearning_en

open Finset
open scoped Classical

variable {X : Type*} [Fintype X]
variable (D : Distribution X)
variable {D}

/-- **Linearity in a right-hand scalar factor**: `E[g · c] = E[g] · c` (the scalar is pulled
out of the weighted sum via `Finset.sum_mul`). Right-hand variant of `sampleExpect_smul`
(which pulls the scalar out on the left). Reused by `chernoff_ineq` (to factor the constant
`e^{−t·a}` out of the expectation of `e^{t·Y}`). -/
theorem sampleExpect_mul_const {n : ℕ} (c : ℝ) (g : (Fin n → X) → ℝ) :
    sampleExpect D (fun S ↦ g S * c) = sampleExpect D g * c := by
  dsimp only [sampleExpect]
  simp only [show ∀ S, sampleWeight D S * (g S * c) = (sampleWeight D S * g S) * c from
               fun _ ↦ by ring]
  rw [← Finset.sum_mul]

/-- **Chernoff-Markov (Chernoff inequality on the exponential)**: for `t > 0`, the
probability that `Y ≥ a` is bounded by `e^{−t·a} · E[e^{t·Y}]`.

    ℙ_S [ Y S ≥ a ] ≤ e^{−t·a} · E_{S∼D^m} [ e^{t·Y S} ].

This is Markov applied to the positive variable `Z = e^{t·Y}` at threshold `e^{t·a}`:
`{Z ≥ e^{t·a}} = {Y ≥ a}` (since `x ↦ e^{t·x}` is strictly increasing for `t > 0`),
hence `ℙ[Y ≥ a] = ℙ[Z ≥ e^{t·a}] ≤ E[Z] / e^{t·a} = e^{−t·a} · E[e^{t·Y}]`.

Direct proof in ℝ-weight: pointwise, the indicator `𝟙{a ≤ Y S}` is `≤ e^{t·(Y S − a)}`
(case `a ≤ Y`: `t·(Y−a) ≥ 0` ⟹ `e^{t·(Y−a)} ≥ e⁰ = 1 = 𝟙` by growth of the exponential;
case `¬(a ≤ Y)`: `𝟙 = 0 ≤ e^{...}`, the exponential being strictly positive). We then pass
through `sampleExpect` (monotonicity `sampleExpect_mono`), and factorise
`e^{t·(Y−a)} = e^{t·Y} · e^{−t·a}` (`Real.exp_add`) where `e^{−t·a}` is constant in `S`,
pulled out via `sampleExpect_mul_const`.

This is **ingredient #1** of the Hoeffding concentration (brick 1/5): a generic Chernoff
bound, valid for any function `Y : (Fin n → X) → ℝ`, independent of the Bernoulli structure
(which only enters at brick 2 via the MGF). -/
theorem chernoff_ineq {n : ℕ} (Y : (Fin n → X) → ℝ) (a : ℝ) (t : ℝ) (ht : 0 < t) :
    sampleProb D (fun S ↦ a ≤ Y S) ≤
      sampleExpect D (fun S ↦ Real.exp (t * Y S)) * Real.exp (-(t * a)) := by
  -- (1) Pointwise: `𝟙{a ≤ Y S} ≤ e^{t·(Y S − a)}` (the only `if`, isolated in a `have`
  -- outside the sum calc, avoiding `Decidable` instance frictions).
  have hind : ∀ S : Fin n → X,
      (if a ≤ Y S then (1 : ℝ) else 0) ≤ Real.exp (t * (Y S - a)) := by
    intro S
    by_cases h : a ≤ Y S
    · -- `Y ≥ a` ⟹ `t·(Y−a) ≥ 0` ⟹ `e^{t·(Y−a)} ≥ e⁰ = 1`.
      rw [if_pos h, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonneg (le_of_lt ht) (sub_nonneg.mpr h))
    · -- `Y < a` ⟹ `𝟙 = 0 ≤ e^{...}` (strictly positive exponential).
      rw [if_neg h]
      exact (Real.exp_pos _).le
  -- (2) `e^{t·(Y−a)} = e^{t·Y} · e^{−t·a}` pointwise (`Real.exp_add`).
  have hexp : ∀ S : Fin n → X,
      Real.exp (t * (Y S - a)) = Real.exp (t * Y S) * Real.exp (-(t * a)) := by
    intro S
    rw [show t * (Y S - a) = t * Y S + (-(t * a)) from by ring, Real.exp_add]
  -- (3) Assembly: `ℙ = E[𝟙] ≤ E[e^{t(Y−a)}] = E[e^{tY}·e^{−ta}] = e^{−ta}·E[e^{tY}]`.
  calc sampleProb D (fun S ↦ a ≤ Y S)
      = sampleExpect D (fun S ↦ (if a ≤ Y S then (1 : ℝ) else 0)) :=
          sampleProb_eq_sampleExpect _
    _ ≤ sampleExpect D (fun S ↦ Real.exp (t * (Y S - a))) :=
        sampleExpect_mono hind
    _ = sampleExpect D (fun S ↦ Real.exp (t * Y S) * Real.exp (-(t * a))) :=
        congr_arg (sampleExpect D) (funext hexp)
    _ = sampleExpect D (fun S ↦ Real.exp (t * Y S)) * Real.exp (-(t * a)) :=
        sampleExpect_mul_const (Real.exp (-(t * a))) (fun S ↦ Real.exp (t * Y S))


/-! ## Bricks 4/5 + 5/5 — two-sided Hoeffding concentration (final iteration)

We assemble the full Hoeffding concentration for the mean of i.i.d. indicators:

    ℙ_S [ |empError f h S − trueError D f h| ≥ ε ] ≤ 2 · exp(−2 · n · ε²).

Decomposition (each ingredient is documented as brick 2-3 of the analysis):

1. `hoeffding_mgf_sum_le` (valid ∀ t ∈ ℝ): `E_S[exp(t · Σ_i(ind_i − μ))] ≤ exp(n · t²/8)`,
   combining **product independence** (`sampleExpect_prod_coord`, brick 3/5), the
   **algebraic reduction** of the MGF (`expect_exp_centered_eq`, brick 2a/5) and the
   **analytic bound** (`bernoulli_mgf_le`, brick 2c/3).
2. `hoeffding_upper_tail` (brick 4/5): `P(Σ_i(ind_i − μ) ≥ n·ε) ≤ exp(−2nε²)` via
   `chernoff_ineq` at `t = 4ε`, the optimisation `t²/8 − t·ε = 2ε² − 4ε² = −2ε²` being done
   by `ring` in the final bound.
3. `hoeffding_lower_tail`: `P(Σ_i(ind_i − μ) ≤ −n·ε) ≤ exp(−2nε²)` — symmetric, via
   `chernoff_ineq` applied to `−Z` and `hoeffding_mgf_sum_le` at `t = −4ε` (legitimate since
   the latter is valid ∀ t, itself a consequence of `bernoulli_mgf_le` ∀ t).
4. `hoeffding_concentration` (brick 5/5, flagship): union of the two tails via
   `sampleProb_or_le`, after rewriting `|empError − μ| ≥ ε` as the disjunction of the two
   tails on `Z = Σ_i(ind_i − μ)` via the identity `empError f h S − μ = Z S / n`.

We stay in the **pedagogical ℝ-weight** style: no `ℝ≥0∞`/`Measure`/`iIndepFun` machinery.
-/

/-- **Union of two events** (binary case of the union bound): the probability of a
disjunction is bounded by the sum of the probabilities. Lighter than
`sampleProb_union_bound` (indexed by a `Finset`) when one has exactly two events — this is
the setting of the two-sided flagship `(Z ≥ nε) ∨ (Z ≤ −nε)`. -/
theorem sampleProb_or_le {n : ℕ} (P Q : (Fin n → X) → Prop) [DecidablePred P] [DecidablePred Q] :
    sampleProb D (fun S ↦ P S ∨ Q S) ≤ sampleProb D P + sampleProb D Q := by
  -- Pointwise: `𝟙{P∨Q} ≤ 𝟙_P + 𝟙_Q` (the only `if`, isolated outside the sums).
  have hind : ∀ S : Fin n → X,
      (if P S ∨ Q S then (1 : ℝ) else 0) ≤
        (if P S then (1 : ℝ) else 0) + (if Q S then (1 : ℝ) else 0) := by
    intro S
    by_cases hP : P S <;> by_cases hQ : Q S <;> simp [hP, hQ] <;> norm_num
  -- Assembly: `ℙ = E[𝟙] ≤ E[𝟙_P + 𝟙_Q] = E[𝟙_P] + E[𝟙_Q] = ℙ_P + ℙ_Q`.
  calc sampleProb D (fun S ↦ P S ∨ Q S)
      = sampleExpect D (fun S ↦ (if P S ∨ Q S then (1 : ℝ) else 0)) := sampleProb_eq_sampleExpect _
    _ ≤ sampleExpect D (fun S ↦ (if P S then (1 : ℝ) else 0) + (if Q S then (1 : ℝ) else 0)) :=
        sampleExpect_mono hind
    _ = sampleExpect D (fun S ↦ (if P S then (1 : ℝ) else 0)) +
        sampleExpect D (fun S ↦ (if Q S then (1 : ℝ) else 0)) := by
        -- Pointwise additivity of `sampleExpect`: we unfold the definition (weighted sum),
        -- then `mul_add` distributes the weight over each indicator and `sum_add_distrib`
        -- splits the sum. Avoids `sampleExpect_linear (1)(1)` whose implicit args `g₁ g₂`
        -- leave a `typeclass problem is stuck` instance.
        dsimp only [sampleExpect]
        simp only [mul_add, Finset.sum_add_distrib]
    _ = sampleProb D P + sampleProb D Q := by
        rw [← sampleProb_eq_sampleExpect P, ← sampleProb_eq_sampleExpect Q]

/-- **Extensionality of `sampleProb`**: two pointwise-equivalent predicates give the same
probability (the `𝟙` indicators coincide pointwise). Reused by `hoeffding_lower_tail`
(event flip `Z ≤ −nε ⟺ nε ≤ −Z`) and `hoeffding_concentration` (decoupling
`|empError − μ| ≥ ε ⟺ (nε ≤ Z) ∨ (Z ≤ −nε)`). Avoids the `DecidablePred` instance frictions
that `congr_arg (sampleProb D)` engenders on the implicit args `{n}` and the instance. -/
theorem sampleProb_congr {n : ℕ} (P Q : (Fin n → X) → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ S, P S ↔ Q S) : sampleProb D P = sampleProb D Q := by
  dsimp only [sampleProb]
  refine Finset.sum_congr rfl (fun S _ ↦ ?_)
  by_cases hP : P S
  · rw [if_pos hP, if_pos ((h S).mp hP)]
  · rw [if_neg hP, if_neg (mt (h S).mpr hP)]

/-- **MGF of the centred sum** (combined brick 3/5 + 2c/3): for `μ = trueError` and
`ind = 𝟙{h≠f}`, the moment-generating function of the empirical centred sum
`Z S = Σ_i (ind(S_i) − μ)` is bounded by `exp(n · t²/8)`, **for all `t ∈ ℝ`**.

    E_{S∼D^m} [ exp (t · Σ_i (ind(S_i) − μ)) ] ≤ exp (n · t²/8).

Proof: `exp(t·Σ_i g_i) = ∏_i exp(t·g_i)` (`Real.exp_sum` after `Finset.mul_sum`), then
**product independence** `sampleExpect_prod_coord` factorises into `∏_i E_D[exp(t·(ind−μ))]`,
each factor reduces algebraically (`expect_exp_centered_eq`) to
`μ·exp(t(1−μ)) + (1−μ)·exp(−tμ)`, bounded by `exp(t²/8)` (`bernoulli_mgf_le`, ∀ t). The
product of the `n` factors `≤ exp(t²/8)` gives `exp(t²/8)^n = exp(n·t²/8)`
(`Real.exp_nat_mul`).

The **∀ t** validity (not only `t > 0`) is crucial: it makes the lower tail immediate
(apply this lemma at `t = −4ε`), since `bernoulli_mgf_le` is itself ∀ t. -/
theorem hoeffding_mgf_sum_le (f h : Hypothesis X) {n : ℕ} (t : ℝ) :
    sampleExpect D (fun S : Fin n → X ↦
      Real.exp (t * (∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - trueError D f h)))) ≤
      Real.exp ((n : ℝ) * t ^ 2 / 8) := by
  set μ := trueError D f h
  have hμ : 0 ≤ μ := trueError_nonneg
  have hμ2 : μ ≤ 1 := trueError_le_one
  -- (1) `exp(t · Σ_i g_i) = ∏_i exp(t · g_i)` pointwise (`mul_sum` pulls out `t`, then `exp_sum`).
  have hexp : ∀ S : Fin n → X,
      Real.exp (t * (∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ))) =
        ∏ i : Fin n, Real.exp (t * ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ)) := by
    intro S
    rw [← Real.exp_sum, ← Finset.mul_sum]
  -- (2) Assembly: product → product independence → algebraic reduction → analytic bound.
  calc sampleExpect D (fun S : Fin n → X ↦
          Real.exp (t * (∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ))))
      = sampleExpect D (fun S : Fin n → X ↦
          ∏ i : Fin n, Real.exp (t * ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ))) := by
          simp only [hexp]
    _ = ∏ i : Fin n,
          expect D (fun x ↦ Real.exp (t * ((if h x ≠ f x then (1 : ℝ) else 0) - μ))) := by
          exact sampleExpect_prod_coord (fun x ↦ Real.exp (t * ((if h x ≠ f x then (1 : ℝ) else 0) - μ)))
    _ = ∏ i : Fin n, (μ * Real.exp (t * (1 - μ)) + (1 - μ) * Real.exp (-(t * μ))) := by
          congr 1
          funext i
          exact expect_exp_centered_eq f h t
    _ ≤ ∏ i : Fin n, Real.exp (t ^ 2 / 8) := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i _; exact bernoulli_mgf_le μ t hμ hμ2
    _ = Real.exp ((n : ℝ) * t ^ 2 / 8) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
          congr 1; ring

/-- **Upper tail of Hoeffding** (brick 4/5): the probability of an excess `Z ≥ n·ε` of the
centred sum `Z = Σ_i(ind_i − μ)` is bounded by `exp(−2·n·ε²)`.

    ℙ_S [ n·ε ≤ Σ_i (ind(S_i) − μ) ] ≤ exp(−2·n·ε²).

Proof: `chernoff_ineq` at `t = 4ε` (`> 0`) bounds `ℙ[Z ≥ nε]` by
`E[exp(4ε·Z)]·exp(−4ε·nε)`. The MGF `hoeffding_mgf_sum_le` (at `t = 4ε`) gives
`E[exp(4ε·Z)] ≤ exp(n·(4ε)²/8) = exp(2nε²)`, hence `exp(2nε²)·exp(−4nε²) = exp(−2nε²)`
(exponent algebra via `Real.exp_add`). -/
theorem hoeffding_upper_tail (f h : Hypothesis X) {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    sampleProb D (fun S : Fin n → X ↦
      ↑n * ε ≤ ∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - trueError D f h)) ≤
      Real.exp (-(2 * ↑n * ε ^ 2)) := by
  set μ := trueError D f h
  set Z : (Fin n → X) → ℝ := fun S ↦ ∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ)
  have ht : 0 < (4 : ℝ) * ε := by positivity
  -- Chernoff-Markov: `ℙ[Z ≥ nε] ≤ E[exp(4ε·Z)] · exp(−4ε·nε)`.
  have hch : sampleProb D (fun S : Fin n → X ↦ ↑n * ε ≤ Z S) ≤
      sampleExpect D (fun S ↦ Real.exp (4 * ε * Z S)) * Real.exp (-(4 * ε * (↑n * ε))) :=
    @chernoff_ineq _ _ D _ Z (↑n * ε) (4 * ε) ht
  -- MGF bounded at `t = 4ε`: `E[exp(4ε·Z)] ≤ exp(2nε²)`.
  have hmgf : sampleExpect D (fun S : Fin n → X ↦ Real.exp (4 * ε * Z S)) ≤
      Real.exp (↑n * (4 * ε) ^ 2 / 8) :=
    hoeffding_mgf_sum_le f h (4 * ε)
  -- `exp(2nε²) · exp(−4nε²) = exp(−2nε²)` (`Real.exp_add` on the exponents).
  calc sampleProb D (fun S ↦ ↑n * ε ≤ Z S)
      ≤ sampleExpect D (fun S ↦ Real.exp (4 * ε * Z S)) * Real.exp (-(4 * ε * (↑n * ε))) := hch
    _ ≤ Real.exp (↑n * (4 * ε) ^ 2 / 8) * Real.exp (-(4 * ε * (↑n * ε))) := by
          -- We bound `A·c ≤ B·c` (c = exp(−4ε·nε) > 0) by `mul_le_mul_of_nonneg_right`.
          -- `gcongr` closes this goal alone without leaving a sub-goal for `exact` (stuck
          -- instance), hence the explicit form `hmgf` + `(Real.exp_pos _).le`.
          exact mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
    _ = Real.exp (-(2 * ↑n * ε ^ 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- **Lower tail of Hoeffding**: the probability of a shortfall `Z ≤ −n·ε` is bounded by
`exp(−2·n·ε²)`.

    ℙ_S [ Σ_i (ind(S_i) − μ) ≤ −n·ε ] ≤ exp(−2·n·ε²).

Proof: `Z ≤ −nε ⟺ −Z ≥ nε`. We apply `chernoff_ineq` to `−Z` at `t = 4ε`:
`ℙ[−Z ≥ nε] ≤ E[exp(4ε·(−Z))]·exp(−4ε·nε)`. Now `E[exp(4ε·(−Z))] = E[exp((−4ε)·Z)] ≤ exp(n·(−4ε)²/8)`
by `hoeffding_mgf_sum_le` at `t = −4ε` (valid ∀ t), i.e. `exp(2nε²)`. We conclude as in the
upper tail. -/
theorem hoeffding_lower_tail (f h : Hypothesis X) {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    sampleProb D (fun S : Fin n → X ↦
      ∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - trueError D f h) ≤ -(↑n * ε)) ≤
      Real.exp (-(2 * ↑n * ε ^ 2)) := by
  set μ := trueError D f h
  set Z : (Fin n → X) → ℝ := fun S ↦ ∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ)
  have ht : 0 < (4 : ℝ) * ε := by positivity
  -- Chernoff-Markov on `−Z` at `t = 4ε`: `ℙ[nε ≤ −Z] ≤ E[exp(4ε·(−Z))]·exp(−4ε·nε)`.
  have hch : sampleProb D (fun S : Fin n → X ↦ ↑n * ε ≤ -Z S) ≤
      sampleExpect D (fun S ↦ Real.exp (4 * ε * (-Z S))) * Real.exp (-(4 * ε * (↑n * ε))) :=
    @chernoff_ineq _ _ D _ (fun S ↦ -Z S) (↑n * ε) (4 * ε) ht
  -- MGF at `t = −4ε` (valid ∀ t, since `bernoulli_mgf_le` is ∀ t): `E[exp(−4ε·Z)] ≤ exp(n·(−4ε)²/8)`.
  have hmgf : sampleExpect D (fun S : Fin n → X ↦ Real.exp (-(4 * ε) * Z S)) ≤
      Real.exp (↑n * (-(4 * ε)) ^ 2 / 8) :=
    hoeffding_mgf_sum_le f h (-(4 * ε))
  have hexpm : ∀ S, Real.exp (4 * ε * (-Z S)) = Real.exp (-(4 * ε) * Z S) := fun S ↦ by congr 1; ring
  -- `Z ≤ −nε ⟺ nε ≤ −Z` (pointwise), then we assemble as in the upper tail.
  calc sampleProb D (fun S ↦ Z S ≤ -(↑n * ε))
      = sampleProb D (fun S ↦ ↑n * ε ≤ -Z S) :=
          sampleProb_congr _ _ (fun S ↦ ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩)
    _ ≤ sampleExpect D (fun S ↦ Real.exp (4 * ε * (-Z S))) * Real.exp (-(4 * ε * (↑n * ε))) := hch
    _ = sampleExpect D (fun S ↦ Real.exp (-(4 * ε) * Z S)) * Real.exp (-(4 * ε * (↑n * ε))) := by
          rw [show ((fun S : Fin n → X ↦ Real.exp (4 * ε * (-Z S))) :
                       (Fin n → X) → ℝ) = (fun S ↦ Real.exp (-(4 * ε) * Z S)) from funext hexpm]
    _ ≤ Real.exp (↑n * (-(4 * ε)) ^ 2 / 8) * Real.exp (-(4 * ε * (↑n * ε))) := by
          exact mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
    _ = Real.exp (-(2 * ↑n * ε ^ 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- **Flagship — two-sided Hoeffding concentration** (brick 5/5): for `n ≥ 1` i.i.d. draws
and `ε > 0`, the probability that the empirical error deviates from its expectation by at
least `ε` is bounded by `2·exp(−2·n·ε²)`.

    ℙ_{S∼D^n} [ |empError f h S − trueError D f h| ≥ ε ] ≤ 2 · exp(−2 · n · ε²).

This is the **central result** of concentration for the mean of i.i.d. Bernoulli indicators
— the exact ingredient which, combined with the union bound over a finite hypothesis class
(`UnionBound_en.lean`), yields Valiant's PAC sample complexity `m ≥ (1/ε)(ln|H|+ln(1/δ))`
(realisable case, brick 3/3) and `1/ε²` (agnostic case).

Proof: `|empError − μ| ≥ ε = (empError − μ ≥ ε) ∨ (μ − empError ≥ ε)`. Via the identity
`empError f h S − μ = Z S / n` (`Z = Σ_i(ind_i − μ)`, `n > 0`), each branch rewrites to a tail
on `Z` bounded by `hoeffding_upper_tail` / `hoeffding_lower_tail`. `sampleProb_or_le` adds the
two tails, giving `2·exp(−2nε²)`. -/
theorem hoeffding_concentration (f h : Hypothesis X) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    sampleProb D (fun S : Fin n → X ↦ ε ≤ |empError f h S - trueError D f h|) ≤
      2 * Real.exp (-(2 * ↑n * ε ^ 2)) := by
  set μ := trueError D f h
  set Z : (Fin n → X) → ℝ := fun S ↦ ∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ)
  have hnreal : (0 : ℝ) < ↑n := mod_cast hn
  -- Key identity: `empError − μ = Z S / n` (`Z = Σ_i(ind_i − μ) = A − nμ`, hence `Z/n = A/n − μ`).
  have hZid : ∀ S : Fin n → X, empError f h S - μ = Z S / (n : ℝ) := by
    intro S
    dsimp only [empError, Z]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp
    ring
  -- Decoupling `|empError − μ| ≥ ε ⟺ (nε ≤ Z) ∨ (Z ≤ −nε)` via `empError − μ = Z/n` (n > 0).
  have hkey : ∀ S : Fin n → X,
      (ε ≤ |empError f h S - μ|) ↔ ((↑n * ε ≤ Z S) ∨ (Z S ≤ -(↑n * ε))) := by
    intro S
    rw [hZid, abs_div, abs_of_pos hnreal, le_div_iff₀ hnreal]
    constructor
    · -- `nε ≤ |Z| → (nε ≤ Z) ∨ (Z ≤ −nε)`
      intro h
      rcases le_total (Z S) 0 with hZ | hZ
      · rw [abs_of_nonpos hZ] at h; exact Or.inr (by linarith)
      · rw [abs_of_nonneg hZ] at h; exact Or.inl (by linarith)
    · -- `(nε ≤ Z) ∨ (Z ≤ −nε) → nε ≤ |Z|`
      rintro (h | h)
      · linarith [le_abs_self (Z S)]
      · have h2 : -Z S ≤ |Z S| := abs_neg (Z S) ▸ le_abs_self (-Z S)
        linarith
  -- Rewrite the event `|empError − μ| ≥ ε` as the disjunction of the two tails on `Z`,
  -- then `sampleProb_or_le` adds them, each bounded by `exp(−2nε²)`.
  calc sampleProb D (fun S ↦ ε ≤ |empError f h S - μ|)
      = sampleProb D (fun S ↦ (↑n * ε ≤ Z S) ∨ (Z S ≤ -(↑n * ε))) :=
          sampleProb_congr _ _ (fun S ↦ hkey S)
    _ ≤ sampleProb D (fun S ↦ ↑n * ε ≤ Z S) + sampleProb D (fun S ↦ Z S ≤ -(↑n * ε)) :=
        sampleProb_or_le (fun S ↦ ↑n * ε ≤ Z S) (fun S ↦ Z S ≤ -(↑n * ε))
    _ ≤ Real.exp (-(2 * ↑n * ε ^ 2)) + Real.exp (-(2 * ↑n * ε ^ 2)) := by
          gcongr
          · exact hoeffding_upper_tail f h hε
          · exact hoeffding_lower_tail f h hε
    _ = 2 * Real.exp (-(2 * ↑n * ε ^ 2)) := by ring

end PacLearning_en

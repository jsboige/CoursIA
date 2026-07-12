import Mathlib
import PacLearning.BernoulliMGF
import PacLearning.Concentration
import PacLearning.Data
import PacLearning.Hoeffding
import PacLearning.MGF
import PacLearning.PacFiniteBound
import PacLearning.Sample
import PacLearning.SampleExpect
import PacLearning.UnionBound

/-!
# PacLearning — PAC theory (Valiant 1984), finite class module, Lean 4

`PacLearning` module of the `learning_theory_lean` lake, sibling of `Perceptron`
(Novikoff's theorem). While `Perceptron` formalizes the **convergence of a
specific algorithm** (the perceptron, `(R/γ)²` bound), `PacLearning` formalizes
**generalization theory** in Valiant's sense (1984): *when* can we guarantee that
a hypothesis that classifies the sample correctly generalizes, and with *how many
examples*?

## The PAC (Probably Approximately Correct) framework

For a finite hypothesis class `H` (over an instance space `X` equipped with a
distribution `D`), the **sample complexity** says: to achieve true error `≤ ε`
with probability `≥ 1 - δ` on a sample `S ∼ D^m`, it suffices to draw

    m ≥ (1/ε) · (ln |H| + ln(1/δ))

i.i.d. examples (Shalev-Shwartz & Ben-David, *Understanding Machine Learning*, §2).
The proof combines:
1. **Hoeffding** — for a fixed hypothesis `h`, `|L_S(h) - L_D(h)|` is concentrated
   around `0` as `m` grows;
2. **Union bound** over the finite class `H` — the probability that **no**
   hypothesis deviates by more than `ε` from its true error is `≥ 1 - δ` once `m`
   exceeds the threshold above.

## Iteration 1 — model + elementary properties (delivered)

- `PacLearning/Data.lean` — distribution `Distribution` (normalized weight `X → ℝ`),
  true error `trueError` (mass of misclassified instances), empirical error
  `empError` (proportion of mistakes on a sample). **Elementary 0-sorry**
  properties, symmetric for both errors: non-negativity (`trueError_nonneg`,
  `empError_nonneg`), upper bound `≤ 1` (`trueError_le_one`, `empError_le_one`),
  zero when `h = f` (`trueError_self`, `empError_self`), `h ↔ f` symmetry
  (`trueError_comm`, `empError_comm`).

## Iteration 2 — sample complexity (in progress, decomposed into bricks)

**Mathlib v4.31.0-rc1 exposes Hoeffding** (`Probability.Moments.SubGaussian`:
`measure_sum_ge_le_of_iIndepFun`, Hoeffding's inequality for sums of independent
sub-Gaussians; `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, Hoeffding
lemma), but within the heavy **Kernel + Measure + ℝ≥0∞ + `HasSubgaussianMGF` +
`iIndepFun`** framework. Wiring the pedagogical discrete distribution
`Distribution X` (`Data.lean`'s ℝ-weight style) into this framework (proving the
i.i.d. independence of the draws, the sub-Gaussianity of the indicators) is
heavier than proving Hoeffding-for-Bernoulli **directly in ℝ-weight** via the
Chernoff method (`log_le_sub_one_of_pos` + Markov on `exp(t · X̄)` + convexity of
`exp`, reusing Mathlib's *lemmas* but not its *framework*). This is a
**pedagogical choice** (readability, consistent with `Data.lean`), not a
necessity — the mathematical result is the true Hoeffding. As atomic 0-sorry
bricks:

- `PacLearning/Sample.lean` (**brick 1/3 delivered**) — product distribution
  `D^m` over the sample space `Fin n → X`: weight `sampleWeight`
  (`∏ i, D.weight (S i)`), non-negativity, **normalization**
  `sampleWeight_sum_one` (`∑ S, sampleWeight D S = 1` via discrete Fubini
  `sum_pow'` then `D.sum_one`). This is the probabilistic setting required to
  speak of i.i.d. draws `S ∼ D^m`.
- `PacLearning/Concentration.lean` (**brick 2a/3 delivered**) —
  expectation `expect` (`∑ x, D.weight x · g x`) + linearity, expectation of
  constants, bridge `trueError_eq_expect`, and **Markov's inequality** in
  ℝ-weight (`markov_ineq`: `D-weight {x | t ≤ g x} ≤ E[g]/t` via
  `Finset.filter` + `Finset.sum_mul` + `mul_le_mul_of_nonneg_left`). Lays the
  foundations of the Chernoff method (brick 2c/3).
- `PacLearning/SampleExpect.lean` (**bricks 2b/3 + 2c/3-partial delivered**) —
  empirical expectation `sampleExpect D g = ∑ S, sampleWeight D S · g S` over the
  sample space `Fin n → X` (extension of `expect` to the product `D^m`), with
  **linearity**, **normalization** `sampleExpect_const`
  (`E_{S∼D^m}[c] = c` via `sampleWeight_sum_one`), non-negativity and monotonicity.
  **And the marginalization of one coordinate** `sampleExpect_coord`
  (`E_{S∼D^m}[g(S i)] = E_D[g]`, key brick via `Fintype.prod_sum` +
  `prod_eq_single_of_mem`): marginalizing one coordinate of the product `D^m`
  recovers `D`. **And the unbiased estimator**
  `sampleExpect_empError_eq_trueError`
  (`E_{S∼D^m}[empError] = trueError`, by linearity + `sampleExpect_coord`
  coordinate-by-coordinate): the empirical error is centered on the true error.
  **And the factorization of a product (i.i.d. independence)**
  `sampleExpect_prod_coord`
  (`E_{S∼D^m}[∏_i h (S i)] = ∏_i E_D[h]`, same skeleton `Fintype.prod_sum` as
  `sampleExpect_coord` but without the `if` — every coordinate carries `h`):
  key ingredient of Hoeffding concentration (brick 3/5); it yields the
  **MGF of a sum = product of MGFs** (`h = exp(t·ind)` ⟹
  `E_S[exp(t·∑_i ind(S_i))] = ∏_i E_D[exp(t·ind)]`). Setting required by Hoeffding
  concentration.
- **Brick 2c/3-remaining — OPEN**: Hoeffding-for-Bernoulli concentration,
  `ℙ_S [ |empError − trueError| > ε ] ≤ 2·exp(−2mε²)` (Chernoff method: Markov on
  `exp(t·(X̄−μ))` + `log t ≤ t − 1` on the indicators).
- `PacLearning/BernoulliMGF.lean` (**brick 2b/5-partial delivered**) — the
  **analytic core** of Hoeffding. Ingredients proven for the final bound
  `μ·exp(t(1−μ)) + (1−μ)·exp(−tμ) ≤ exp(t²/8)`: Bernoulli variance `μ(1−μ) ≤ 1/4`
  (`bernoulli_var_le`, unconditional by completing the square), positivity + MGF
  normalization, and the **symmetric case `μ = 1/2`** `bernoulli_mgf_half_le` via
  `cosh x ≤ exp(x²/2)` (Mathlib `cosh_le_exp_half_sq`). The general bound for
  arbitrary `μ ∈ [0,1]` is documented OPEN: it requires the variational route
  (Donsker–Varadhan + Pinsker) or second-derivative (tilted cgf), heavy outside
  Mathlib's Measure framework.
- `PacLearning/UnionBound.lean` (**brick 3/3-combinatorial half delivered**) —
  **combinatorial half** of the flagship `pac_finite_class_bound`. Probability of
  an event over the sample space `sampleProb` (`E[𝟙{Q}]`) + Finset-indexed
  linearity `sampleExpect_finset_sum`, and above all the **union bound (Boole's
  inequalities)** `sampleProb_union_bound`:
  `ℙ_S[∃ i ∈ s, P i S] ≤ ∑_{i ∈ s} ℙ_S[P i S]`, 0-sorry (indicator(∃) ≤ ∑
  indicators pointwise via `Finset.single_le_sum`, then monotonicity + linearity
  of `sampleExpect`).
- `PacLearning/PacFiniteBound.lean` (**brick 3/3 DELIVERED — realizable case**):
  flagship theorem `pac_finite_class_bound` (Valiant 1984, `m ≥ (1/ε)(ln|Hs| +
  ln(1/δ))`), proof closed. Combines `sampleProb_consistent_le` (`(1−μ)^n`) +
  `one_sub_pow_le_exp` (`(1−μ)^n ≤ exp(−εn)`) + **union bound at the
  `sampleExpect` level** (working around the `Decidable` synthesis blowup on
  `∃ hyp ∈ Hs, …` which enumerates `Hypothesis X = X → Bool` via
  `decidableExistsAndFinsetCoe`: explicit `hDec` instance + `@ite` annotation +
  `Classical.em`, `pacDecidable` symbol for the defeq wrapper).
- **Brick 3/3-remaining — OPEN (agnostic case)**: agnostic bound
  `m ≥ (1/(2ε²))·(ln(2|H|/δ))` (Shalev-Shwartz–Ben-David §2.4), requires the
  Hoeffding-for-Bernoulli concentration `ℙ[|empError − trueError| > ε] ≤
  2·exp(−2nε²)`, blocked on the general MGF bound (2b/5, variational route OPEN
  in `BernoulliMGF.lean`).

## Reference

- L. G. Valiant, *A theory of the learnable*, Communications of the ACM **27**
  (1984).
- S. Shalev-Shwartz & S. Ben-David, *Understanding Machine Learning*, Cambridge
  University Press (2014), §2 (finite hypothesis classes) and §6 (VC dimension).
- See issue #4293 (Lean roadmap #4038).
-/

namespace PacLearning_en

/-- Status: iteration 1 delivered (model + elementary properties 0-sorry);
iteration 2 — **bricks 1/3, 2a/3, 2b/3, 2c/3 delivered + 3/3 DELIVERED (realizable
case, `pac_finite_class_bound` in `PacFiniteBound.lean`)**
(`Sample.lean`: product distribution `D^m` + normalization; `Concentration.lean`:
`expect`, `markov_ineq`; `SampleExpect.lean`: `sampleExpect` + linearity/normalization
+ **coordinate marginalization `sampleExpect_coord`** + **unbiased estimator
`sampleExpect_empError_eq_trueError`** + **product factorization (i.i.d. independence)
`sampleExpect_prod_coord`**; `UnionBound.lean`: `sampleProb` + **union bound
(Boole's inequalities) `sampleProb_union_bound`**; `MGF.lean`: **algebraic reduction
of the centered MGF `expect_exp_centered_eq`** (first sub-brick of Hoeffding:
`E_D[exp(t(ind−μ))] = μ·exp(t(1−μ)) + (1−μ)·exp(−tμ)`, 0-analysis); `BernoulliMGF.lean`:
**Hoeffding analytic core** — `bernoulli_var_le` (variance `μ(1−μ)≤1/4`),
`bernoulli_mgf_half_le` (symmetric case via `cosh x ≤ exp(x²/2)`), positivity + MGF
normalization. Remaining bricks (**agnostic** case only — the realizable one is
delivered): general MGF bound `μ·exp(t(1−μ))+(1−μ)·exp(−tμ) ≤ exp(t²/8)` (hard
analytic 2b/5, variational route OPEN) + two-sided Hoeffding concentration +
agnostic bound `m ≥ (1/(2ε²))·(ln(2|H|/δ))`. The **realizable case**
`pac_finite_class_bound` (`m ≥ (1/ε)(ln|Hs|+ln(1/δ))`) is DELIVERED (proof closed,
axiom-free) in `PacFiniteBound.lean`. -/
abbrev Status : Prop := True

end PacLearning_en

/-!
English mirror of `PacLearning.lean` (FR-first canonical), EPIC #4980 (i18n Lean).
Convention ratified 2026-07-04 (issue #4980): distinct FR + EN sibling files in the
same lake; namespace `PacLearning_en` (anti-collision with the FR `PacLearning`
namespace); non-docstring proof code unchanged.
-/

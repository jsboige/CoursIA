# LearningTheory — English companion (i18n Option B)

> **i18n Option B companion** — the `.lean` files of the lake `learning_theory_lean`
> (under `MyIA.AI.Notebooks/ML/learning_theory_lean/`) keep their **French
> docstrings** as the single source of truth; this `.en.md` file is a
> **non-compiled markdown mirror** of the same docstrings translated to English.
> Following the rollout convention decided by the user on 2026-07-02 (pilot
> `#4998` MERGED, see `#4980`).

Lake: `learning_theory_lean` (Mathlib v4.31.0-rc1), family **ML**.
Two top-level modules: `Perceptron` (Novikoff's convergence theorem) and
`PacLearning` (Valiant's PAC theory, finite class, agnostic iter-2).

- **Source canonique (FR, inchangée)** : tous les fichiers `.lean` ci-dessous.
- **Compagnon (EN, ce fichier)** : miroir markdown non compilé.
- **Convention** : `README.md` → `README.en.md` (cf. `#1650`). Zéro coût
  `lake build`, zéro risque compil.

---

## `lakefile.lean`

```
package «learning_theory_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"
```

Lake declaration. Two `lean_lib` targets, each pulling in its submodules:

- **`Perceptron`** (default target) — Novikoff's convergence theorem for the
  perceptron algorithm on linearly separable data with margin `γ` and radius
  `R`: at most `(R/γ)²` updates (mistakes) before convergence. The proof is
  geometric and **entirely 0-sorry**.
- **`PacLearning`** (default target) — Valiant's PAC theory (1984), finite
  hypothesis class. Sibling of `Perceptron` in the general-purpose `ML` lake
  `learning_theory_lean` (cf. `decision_theory_lean` which mutualises Gittins +
  Utility + Coherence; see `#4293`).

Mathlib is pinned to `v4.31.0-rc1` (cf. `#4364`).

---

## `Perceptron.lean`

### Pedagogical Lean mini-project: Perceptron convergence (Novikoff's theorem)

Lean 4 project (with Mathlib) proving **Novikoff's convergence theorem** (1962):
for a linearly separable dataset of margin `γ` and radius `R`, the perceptron
algorithm performs at most `(R/γ)²` updates (classification errors) before
converging. See issue `#4051` (Lean roadmap `#4038`).

**First Lean theorem of the `ML` series.** The proof is **geometrically
elementary**:

- the alignment of the weight vector `w` with the separator `u` grows by at
  least `γ` at every error (`⟨w k, u⟩ ≥ k·γ`),
- the norm `‖w k‖²` grows by at most `R²` at every error (`‖w k‖² ≤ k·R²`),
- Cauchy–Schwarz combines the two: `k·γ ≤ ‖w k‖·‖u‖ ≤ √k·R`,
  whence `k ≤ (R/γ)²`.

Mathlib provides `InnerProductSpace`, Cauchy–Schwarz (`abs_inner_le_norm`), and
all the real pre-Hilbert space calculus required; the bound follows from a few
lemmas.

**Model.** We work in an abstract real pre-Hilbert space `V` (Novikoff is
dimension-independent); the data are a finite sequence of points `ℕ → V` with
labels `±1`, a unit separator `u` with margin `γ`, and a radius `R`.

Companion notebook (`ML/ML.Net` series): pedagogical presentation of linear
classification / perceptron. The notebook wiring is the responsibility of the
`ML` series owner (sibling-lake convention: the lake is the formal deliverable,
`lake build` is the execution proof).

---

## `Perceptron/Data.lean`

### Perceptron data — real pre-Hilbert space, points, labels

Novikoff's theorem (1962) is proved in an **abstract real pre-Hilbert space**
`V` (the `(R/γ)²` bound is dimension-independent). This file collects the
elementary geometric facts about norm and inner product required for the proof,
in particular the expansion

```
‖a + b‖² = ‖a‖² + 2·⟪a, b⟫ + ‖b‖²
```

which is the heart of Lemma B (growth of the weight-vector norm).

The data themselves (sequence of points `xₖ`, labels `yₖ ∈ {±1}`, unit
separator `u` with margin `γ`, radius `R`) are modelled in `Perceptron.lean`
by the structure `PerceptronRun`.

**Key declarations.**

- `norm_sq_eq_inner_self` — `‖x‖² = ⟪x, x⟫_ℝ` (the square of the norm coincides
  with the self inner product).
- `norm_add_sq_eq` — expansion of the square of the norm of a sum. **Central
  identity of Lemma B** of Novikoff.
- `IsLabel` — a real scalar whose square is `1` (i.e. `±1`).
- `LabeledPoint` — a vector `x ∈ V` and its label `y ∈ {±1}`.

---

## `Perceptron/Perceptron.lean`

### The perceptron and its execution — weight vector and valid runs

The perceptron update rule: on a classification error at `(xₖ, yₖ)`, the weight
vector evolves via

```
w_{k+1} = wₖ + yₖ · xₖ        (w₀ = 0)
```

The sequence `perceptronWeights` encodes this evolution. A **valid run**
(`PerceptronRun`) records that we take `n` consecutive updates, each being a
**mistake** (`yₖ · ⟨wₖ, xₖ⟩ ≤ 0`), on data of radius `R` separated by a unit
vector `u` with margin `γ`.

These two invariants (mistake + margin) are exactly what makes Novikoff's proof
work: the mistake caps the growth of `‖w‖`, the margin guarantees that of
`⟨w, u⟩`.

**Key declarations.**

- `perceptronWeights` — sequence of weight vectors after `k` updates:
  `w₀ = 0`, `w_{k+1} = wₖ + yₖ · xₖ`.
- `perceptronWeights_zero` — `w₀ = 0`.
- `perceptronWeights_succ` — recursive step.
- `PerceptronRun` — a **valid run of the perceptron** on linearly separable
  data: `n` consecutive updates, each a mistake, on points of radius `R`
  separated by a unit vector `u` with margin `γ`. The structure bundles `n`,
  `pts`, `lbl`, `u`, `R`, `γ`, plus the validity proofs `hR`, `hγ`, `hUnit`,
  `hLbl`, `hRad`, `hMargin`, `hMistake`.
- `PerceptronRun.w` — abbreviation for the weight vector before the `k`-th
  update.

---

## `Perceptron/Convergence.lean`

### Convergence theorem of the Perceptron (Novikoff, 1962) — bound `(R/γ)²`

> **Theorem (Novikoff).** Let a valid execution of the perceptron run on data
> linearly separable by a unit vector `u` with margin `γ > 0`, the points being
> of norm `≤ R`. Then the number of updates (errors) `n` satisfies
> `n ≤ (R/γ)²`.

The proof is **geometrically elementary and entirely 0-sorry**, resting on two
growth inequalities of the weight vector `wₖ` combined by Cauchy–Schwarz:

- **Lemma A — alignment** (`align_growth`): `⟪wₖ, u⟫ ≥ k·γ`. Each error adds
  `yₖ · xₖ` to `w`, and the margin hypothesis guarantees
  `yₖ · ⟪u, xₖ⟫ ≥ γ`, so the alignment on the separator grows by at least `γ`.
- **Lemma B — norm** (`norm_bound`): `‖wₖ‖² ≤ k·R²`. Each error adds at most
  `R²` to `‖w‖²` (via the expansion
  `‖a + b‖² = ‖a‖² + 2⟪a,b⟫ + ‖b‖²`), the cross term being `≤ 0` because the
  update is a mistake (`yₖ · ⟪wₖ, xₖ⟫ ≤ 0`).
- **Conclusion.** Cauchy–Schwarz `⟪wₙ, u⟫ ≤ ‖wₙ‖·‖u‖ = ‖wₙ‖` (with `‖u‖ = 1`)
  gives `n·γ ≤ ‖wₙ‖`, hence `(n·γ)² ≤ ‖wₙ‖² ≤ n·R²`, i.e. `n·γ² ≤ R²`.

Reference: A. B. J. Novikoff, *On convergence proofs for perceptrons*,
Symposium on the Mathematical Theory of Automata (1962).

---

## `Perceptron/Tightness.lean`

### Sharpness of Novikoff's bound — a tight witness

> **Result.** Novikoff's bound `n · γ² ≤ R²` (i.e. `n ≤ (R/γ)²` updates) is
> **optimal**: we exhibit a valid execution of the perceptron, on `ℂ` viewed
> as a 2-dimensional real pre-Hilbert space, that **saturates** the bound —
> `n · γ² = R²` exactly. A universal constant strictly smaller than `1` in
> front of `(R/γ)²` can therefore not majorise the number of errors on all
> separable executions.

**Geometric witness.** Two points `x₀ = 1 + I`, `x₁ = 1 − I` (half-lines at
±45°), both of label `+1`, separated by the unit vector `u = 1` with margin
`γ = 1`, each of norm `‖xₖ‖ = √2` (so `R = √2`). The first update makes
`w₁ = x₀ = 1 + I`; at the second step,
`⟪w₁, x₁⟫ = ⟨1 + I, 1 − I⟩ = 0` (the two half-lines are orthogonal): `x₁`
is exactly on the decision boundary of `w₁`, so the update is a mistake. We
then get `n · γ² = 2 · 1 = 2 = (√2)² = R²`: **equality** — the bound is
attained, hence sharp.

The space `ℂ` carries the instance `InnerProductSpace ℝ ℂ`; the real inner
product unfolds via `⟪w, z⟫_ℝ = (z · conj w).re` (`Complex.inner` +
`Complex.starRingEnd_apply`), i.e. `w.re · z.re + w.im · z.im`, and the
norms via `‖z‖² = Complex.normSq z = z.re² + z.im²`
(`Complex.normSq_eq_norm_sq`, `Complex.normSq_apply`).

This module is **entirely sorry-free**: it is a concrete *sharpness* result
(equality attained), distinct from the universal bound theorem
`novikoff_mistake_bound` (inequality) proved in `Convergence.lean`.

**Key declarations.**

- `complex_inner_re` — real inner product on `ℂ` unfolded in coordinates:
  `⟪w, z⟫ = w.re·z.re + w.im·z.im` (utility lemma for the concrete witness
  computations).
- `witnessPts` — the witness points: `x₀ = 1 + I`, `xₖ = 1 − I` for `k ≥ 1`
  (two half-lines at ±45° of the complex plane).
- `witnessLbl` — the witness labels: all `+1`.
- `witnessPts_norm_sq` — `‖xₖ‖² = 2` for all `k` (both half-lines have the
  same norm `√2`).

---

## `PacLearning.lean`

### PacLearning — PAC theory (Valiant 1984), finite-class module, Lean 4

Module `PacLearning` of the lake `learning_theory_lean`, sibling of
`Perceptron` (Novikoff's theorem). Whereas `Perceptron` formalises the
**convergence of a specific algorithm** (the perceptron, bound `(R/γ)²`),
`PacLearning` formalises **generalisation theory** in Valiant's sense (1984):
*when* can we guarantee that a hypothesis well-classified on the sample
generalises, and *with how many examples*?

#### PAC framework (Probably Approximately Correct)

For a finite hypothesis class `H` (on an instance space `X` endowed with a
distribution `D`), the **sample complexity** states: to reach true error
`≤ ε` with probability `≥ 1 − δ` on a sample `S ∼ D^m`, it suffices to take

```
m ≥ (1/ε) · (ln |H| + ln(1/δ))
```

i.i.d. examples (Shalev-Shwartz & Ben-David, *Understanding Machine
Learning*, §2). The proof combines:

1. **Hoeffding** — for a fixed hypothesis `h`, `|L_S(h) - L_D(h)|` is
   concentrated around `0` as `m` grows;
2. **Union bound** over the finite class `H` — the probability that **no**
   hypothesis deviates by more than `ε` from its true error is `≥ 1 - δ` as
   soon as `m` exceeds the threshold above.

#### Iteration 1 — model + elementary properties (delivered)

- `PacLearning/Data.lean` — distribution `Distribution` (normalised weight
  function `X → ℝ`), true error `trueError` (mass of misclassified
  instances), empirical error `empError` (proportion of errors on a sample).
  **Elementary 0-sorry** properties, symmetric for both errors:
  non-negativity (`trueError_nonneg`, `empError_nonneg`), upper bound `≤ 1`
  (`trueError_le_one`, `empError_le_one`), nullity when `h = f`
  (`trueError_self`, `empError_self`), symmetry `h ↔ f`
  (`trueError_comm`, `empError_comm`).

#### Iteration 2 — sample complexity (in progress, decomposed into bricks)

Mathlib v4.31.0-rc1 exposes Hoeffding
(`Probability.Moments.SubGaussian`: `measure_sum_ge_le_of_iIndepFun`, Hoeffding's
inequality for sums of independent sub-Gaussians;
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, Hoeffding's lemma), but in
the heavy **Kernel + Measure + ℝ≥0∞ + `HasSubgaussianMGF` + `iIndepFun`**
framework. Wiring the pedagogical discrete distribution `Distribution X`
(`ℝ`-weight style of `Data.lean`) into that framework (proving i.i.d.
independence of the draws, sub-Gaussianity of the indicators) is heavier than
proving Hoeffding-for-Bernoulli **directly in `ℝ`-weight** via the Chernoff
method (`log_le_sub_one_of_pos` + Markov on `exp(t · X̄)` + convexity of
`exp`, reusing Mathlib's *lemmas* but not its *framework*). This is a
**pedagogical choice** (readability, consistent with `Data.lean`), not a
necessity — the mathematical result is the true Hoeffding. By atomic bricks
(the Chernoff route is documented in the `MGF` and `Hoeffding` sub-modules).

#### Iteration 2 — flagship agnostic (delivered)

The **agnostic generalisation bound** for an ERM `ĥ` and any reference
hypothesis `hOpt ∈ Hs`,

```
ℙ_{S∼D^n} [ trueError D f (ĥ S) ≤ trueError D f hOpt + 2·ε ] ≥ 1 − 2·|Hs|·exp(−2·n·ε²),
```

combines two bricks:

1. `uniform_concentration` (UniformConcentration.lean, brick 6a) bounds the
   "bad" event (there exists an unconcentrated hypothesis):
   `ℙ[∃ h ∈ Hs, ε ≤ |empError − trueError|] ≤ 2·|Hs|·exp(−2nε²)`.
2. `erm_error_bound` (ERM.lean, brick 6b) is the deterministic argument: on
   the "good" event (`∀ h ∈ Hs, |empError − trueError| ≤ ε`), the ERM
   generalises:
   `trueError(ĥ) ≤ trueError(hOpt) + 2ε`.

The assembly is in `Agnostic.lean`. Inverting `1−δ = 1−2|Hs|exp(−2nε²)` yields
the **agnostic** sample complexity `m ≥ (1/ε²)(ln|H|+ln(1/δ))` — to be
compared with the realisable `m ≥ (1/ε)(ln|H|+ln(1/δ))`
(`pac_finite_class_bound`, PR `#4580`), where the factor `1/ε` (vs `1/ε²`)
reflects geometric concentration `(1−μ)^n ≤ e^{−εn}` rather than the quadratic
Hoeffding concentration.

---

## `PacLearning/Data.lean`

### PacLearning.Data — PAC model: instance space, distribution, errors

**PAC framework** (Valiant 1984, *A theory of the learnable*) for a finite
hypothesis class. We set the probabilistic model on a finite instance type
`X`: a **distribution** (normalised weight function `D : X → ℝ`,
`∑ D x = 1`, `D ≥ 0`), a **target concept** `f : X → Bool`, and a **hypothesis**
`h : X → Bool`.

- **True error** `trueError D f h := ∑ x, if h x ≠ f x then D.weight x else 0`
  — mass (under `D`) of the instances misclassified by `h` (vs the concept
  `f`).
- **Empirical error** `empError f h S` — proportion of errors of `h` on a
  sample `S : Fin n → X`.

We deliberately avoid the `ℝ≥0∞` / `Measure` machinery: for a finite
instance type, the normalised `ℝ`-weight function suffices and keeps the
model readable. This is the discrete counterpart of `PMF.toMeasure`, adapted
to the pedagogy of the bound.

This first deliverable lays down the **model** and the **elementary
properties** of the errors (bounds `[0, 1]`, zero error when `h = f`). The
**sample complexity bound** `pac_finite_class_bound` (Hoeffding on the
empirical error + union bound on the finite class ⟹
`m ≥ (1/ε)(ln|H| + ln(1/δ))`) is **iteration 2+** — documented OPEN, not
sorry-backed.

**Key declarations.**

- `Distribution` — a probability distribution on `X` (finite): normalised
  weight function. We avoid the `ℝ≥0∞` / `Measure` machinery to keep the
  pedagogical model in `ℝ`.
- `Hypothesis` — hypotheses and target concept are functions `X → Bool`
  (binary labels `±1`).
- `trueError`, `empError` — true and empirical errors of `h` vs the concept
  `f` under the distribution `D` (resp. on the sample `S`).

---

## `PacLearning/Sample.lean`

### PacLearning.Sample — product distribution on the sample space

Sub-module of `PacLearning`: we endow the space of **samples**
`Fin n → X` (sequences of `n` instances drawn i.i.d. according to `D`) with
a **product distribution** `D^m`, the discrete counterpart of the tensor
product of measures. This is the probabilistic framework required by the
sample complexity bound `pac_finite_class_bound` (iteration 2+): Hoeffding
concentration of the empirical error is proved on independent draws
`S ∼ D^m`.

We stay in the **pedagogical `ℝ`-weight style** (no `ℝ≥0∞` / `Measure`):
the weight of a sample `S` is the product of the weights of its components,

```
sampleWeight D S = ∏ i : Fin n, D.weight (S i),
```

and the **normalisation** `∑ S, sampleWeight D S = 1` (lemma
`sampleWeight_sum_one`) guarantees that `D^m` is indeed a distribution. The
proof = discrete Fubini identity
`(∑ x, w x)^n = ∑ S, ∏ i, w (S i)`, available in Mathlib as `sum_pow'`
(multinomial expansion: product of sums over a finite type).

This deliverable is **brick 1/3 of iter-2**: the sample model and its
product distribution. The Hoeffding-for-Bernoulli concentration (brick
2/3) and the final bound `pac_finite_class_bound` (brick 3/3) follow.

---

## `PacLearning/BernoulliMGF.lean`

### Bernoulli moment-generating function (MGF), Chernoff route

A Bernoulli variable `X ∈ {0, 1}` of parameter `μ` has MGF

```
M_X(t) = 1 − μ + μ · exp(t).
```

The Chernoff method bounds `ℙ[X̄ − μ ≥ ε]` by `exp(−m·ε² / 2)` (Hoeffding
for Bernoulli) via the chain Markov + convexity of `exp`. This is the
pedagogical route that avoids Mathlib's full sub-Gaussian framework while
preserving the mathematical content.

---

## `PacLearning/Concentration.lean`

### Concentration of the empirical mean around its expectation

Concentration inequality for the empirical mean of bounded i.i.d. variables.
Combined with the union bound over the finite class `H`, this gives the
deviation bound on the empirical error of any fixed hypothesis in `H`.

---

## `PacLearning/MGF.lean`

### Moment-generating function utilities

General utilities for MGFs (Markov inequality, Chernoff bound), independent
of the specific Bernoulli structure. These lemmas are reused by
`BernoulliMGF.lean` and `Hoeffding.lean`.

---

## `PacLearning/Hoeffding.lean`

### Hoeffding-for-Bernoulli, Chernoff route

Hoeffding's inequality for the empirical mean of bounded i.i.d. variables,
proved directly via the Chernoff method (Markov on `exp(t · X̄)` + convexity
of `exp`). The statement is the **true Hoeffding**; the route is
pedagogical (`ℝ`-weight, no `ℝ≥0∞` / `Measure` / `iIndepFun`).

---

## `PacLearning/PacFiniteBound.lean`

### `pac_finite_class_bound` — finite-class sample complexity (iter-2 flagship)

The sample complexity bound for a finite hypothesis class `H`:

```
m ≥ (1/ε) · (ln |H| + ln(1/δ))
```

examples suffice to reach true error `≤ ε` with probability `≥ 1 − δ`. The
proof combines Hoeffding-on-Bernoulli (per fixed `h ∈ H`) and union bound
(over the finite `H`).

---

## `PacLearning/SampleExpect.lean`

### Expectation of a sample statistic

The expectation (under the product distribution `D^m`) of statistics of the
sample `S`, such as the empirical error of a fixed hypothesis `h`. These
identities are used in Hoeffding's inequality to relate the empirical error
to its expectation.

---

## `PacLearning/UnionBound.lean`

### Union bound over a finite family of events

Standard union bound: for events `E_i` of probability `p_i`, the probability
of their union is `≤ ∑ p_i`. Used in `pac_finite_class_bound` to pass from
"each fixed `h ∈ H` is concentrated" to "the whole class is uniformly
concentrated".

---

## `PacLearning/UniformConcentration.lean`

### Uniform concentration over a finite class (brick 6/6-agnostic, step a)

**Brick 6/6-agnostic, step a** of iter-2: the "bad" event — there exists an
unconcentrated hypothesis in `Hs` — is bounded by

```
ℙ[∃ h ∈ Hs, ε ≤ |empError − trueError|] ≤ 2·|Hs|·exp(−2nε²).
```

This is the cornerstone of the agnostic bound; combined with
`erm_error_bound` (brick 6/6-agnostic, step b), it yields the agnostic
generalisation bound assembled in `Agnostic.lean`.

---

## `PacLearning/ERM.lean`

### PacLearning.ERM — Empirical Risk Minimization argument (brick 6/6-agnostic, step b)

Sub-module of `PacLearning`: the deterministic argument at the heart of
**agnostic generalisation**. Given a sample `S`, an ERM hypothesis `ĥ` (that
minimises the empirical error on `S`) and a reference hypothesis `h* ∈ Hs`,
the true error of `ĥ` is controlled by that of `h*` up to `2ε`,
**provided that uniform concentration holds** on the class `Hs`:

```
trueError D f ĥ ≤ trueError D f h* + 2·ε.
```

This is a **purely arithmetic** result (4 elementary inequalities chained) —
it invokes no probabilistic structure. The role of probabilities is played
by the hypothesis
`hconc : ∀ h ∈ Hs, |empError f h S − trueError D f h| ≤ ε`, which is exactly
the event "uniform concentration holds" — whose violation probability is
bounded by `2·|Hs|·exp(−2nε²)` by `uniform_concentration`
(UniformConcentration.lean, brick 6a).

Specialising `h*` to the `argmin` of `trueError` over `Hs` (the best
hypothesis of the class) yields the agnostic generalisation bound: the ERM
does no worse than `2ε` beyond the optimum of the class. Combined with
`uniform_concentration`, this gives the **agnostic** sample complexity
`m ≥ (1/ε²)(ln|H|+ln(1/δ))` — to be compared with the realisable
`m ≥ (1/ε)(ln|H|+ln(1/δ))` (delivered in `pac_finite_class_bound`,
PR `#4580`), where the factor `1/ε` (vs `1/ε²`) reflects geometric
concentration `(1−μ)^n ≤ e^{−εn}` rather than quadratic Hoeffding
concentration.

**Chain of inequalities (the essence of ERM):**

1. **Concentration of `ĥ`**: `|empError(ĥ) − trueError(ĥ)| ≤ ε`
   ⟹ `trueError(ĥ) ≤ empError(ĥ) + ε`.
2. **ERM**: `empError(ĥ) ≤ empError(h*)` (because `ĥ` minimises `empError`
   on `Hs`, and `h* ∈ Hs`).
3. **Concentration of `h*`**: `|empError(h*) − trueError(h*)| ≤ ε`
   ⟹ `empError(h*) ≤ trueError(h*) + ε`.
4. **Combination**: `trueError(ĥ) ≤ empError(ĥ) + ε ≤ empError(h*) + ε ≤ trueError(h*) + 2ε`.

We stay in the **pedagogical `ℝ`-weight style**: no `ℝ≥0∞`/`Measure`/
`iIndepFun` machinery.

---

## `PacLearning/Agnostic.lean`

### PacLearning.Agnostic — agnostic PAC generalisation bound (flagship iter-2)

#### Assembly: uniform_concentration + erm_error_bound

Sub-module of `PacLearning`: the **agnostic flagship** of iteration 2 — the
PAC generalisation bound for a finite hypothesis class `Hs` in the
**agnostic** regime (the target hypothesis `f` is not necessarily in `Hs`).
We prove that, for an ERM `ĥ` (selected as a function of the sample `S`)
and any reference hypothesis `hOpt ∈ Hs`,

```
ℙ_{S∼D^n} [ trueError D f (ĥ S) ≤ trueError D f hOpt + 2·ε ] ≥ 1 − 2·|Hs|·exp(−2·n·ε²).
```

This is the **agnostic generalisation bound**: with probability `≥ 1−δ` on
the sample, the true error of the ERM does not exceed that of the best
hypothesis of the class by more than `2ε`. Specialising `hOpt` to
`argmin_{h∈Hs} trueError D f h` (the best of the class) gives the standard
generalisation theorem. Inverting `1−δ = 1−2|Hs|exp(−2nε²)` yields the
**agnostic** sample complexity `m ≥ (1/ε²)(ln|H|+ln(1/δ))` — to be
compared with the realisable `m ≥ (1/ε)(ln|H|+ln(1/δ))`
(`pac_finite_class_bound`, PR `#4580`), where the factor `1/ε` (vs `1/ε²`)
reflects geometric concentration `(1−μ)^n ≤ e^{−εn}` rather than the
quadratic Hoeffding concentration.

**Assembly** (both ingredients are delivered on main):

1. `uniform_concentration` (UniformConcentration.lean, brick 6a) bounds the
   probability of the "bad" event (there exists an unconcentrated
   hypothesis):
   `ℙ[∃ h ∈ Hs, ε ≤ |empError − trueError|] ≤ 2·|Hs|·exp(−2nε²)`.
2. `erm_error_bound` (ERM.lean, brick 6b) is the deterministic argument: on
   the "good" event (`∀ h ∈ Hs, |empError − trueError| ≤ ε`), the ERM
   generalises:
   `trueError(ĥ) ≤ trueError(hOpt) + 2ε`.
3. This module connects the two: by contrapositive of `erm_error_bound`,
   the event `trueError(ĥ) > trueError(hOpt) + 2ε` implies
   `∃ h ∈ Hs, ε < |empError − trueError|`.

---

## References

- A. B. J. Novikoff, *On convergence proofs for perceptrons*, Symposium on
  the Mathematical Theory of Automata (1962).
- L. G. Valiant, *A theory of the learnable*, Communications of the ACM
  (1984).
- S. Shalev-Shwartz & S. Ben-David, *Understanding Machine Learning:
  From Theory to Algorithms*, Cambridge University Press, §2 (sample
  complexity).
- Mathlib v4.31.0-rc1, `Topology.Sion`, `Probability.Moments.SubGaussian`,
  `InnerProductSpace`, `abs_inner_le_norm`, `real_inner_self_eq_norm_sq`,
  `Complex.inner`, `Complex.normSq_eq_norm_sq`, `Finset.sum_pow'`,
  `log_le_sub_one_of_pos`.
- Issues `#4038` (Lean roadmap), `#4037`, `#4036`, `#4051`, `#4293`,
  `#4364`, `#4580`, `#4980`, `#1650`, `#4208`.

## Lake status

- **Real sorry count (token-grep FX-7)**: 0 before, 0 after.
  - `Perceptron` — 0 sorry (Novikoff `n ≤ (R/γ)²`, fully proved, plus
    tightness witness on `ℂ`).
  - `PacLearning` — 0 sorry (model, Hoeffding-Bernoulli Chernoff route,
    finite-class bound `pac_finite_class_bound`, agnostic assembly
    `uniform_concentration` + `erm_error_bound`).
- **Mathlib pin**: `v4.31.0-rc1` (cf. `#4364`).

---

*Convention i18n Option B — `See #4980`, `#1650`. Single source of truth =
the `.lean` files (FR docstrings). This companion is the EN mirror, not
compiled, anti-regression Lean preserved.*
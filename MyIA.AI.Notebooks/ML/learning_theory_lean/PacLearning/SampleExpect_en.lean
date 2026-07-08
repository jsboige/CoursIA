import Mathlib
import PacLearning.Data_en
import PacLearning.Sample_en
import PacLearning.Concentration_en

/-!
# PacLearning.SampleExpect — empirical expectation over the sample space

Submodule of `PacLearning`: **brick 2b/3** of iter-2. We extend the expectation
framework of `Concentration.lean` (which defined `expect D g` over `X`) to the
**sample space** `Fin n → X` equipped with the product distribution `D^m`
(see `Sample.lean`). The empirical expectation of a function `g : (Fin n → X) → ℝ`
is the weighted sum

    sampleExpect D g = ∑ S, sampleWeight D S · g S.

## This deliverable (brick 2b/3) — the empirical-expectation framework

We define `sampleExpect` and its **elementary properties (entirely proven)**:
non-negativity (`sampleExpect_nonneg`), linearity (`sampleExpect_linear`), and above
all the **normalization** `sampleExpect_const` (`E_{S∼D^m}[constant c] = c`, via
`sampleWeight_sum_one` — `D^m` is indeed a probability distribution). Plus
**monotonicity** (`sampleExpect_mono`). This is the natural extension of `expect`
to the product space, the framework required by any concentration inequality on the
sample.

## This deliverable — marginalization of a coordinate (brick 2c/3, partial)

We prove the **marginalization of a coordinate** `sampleExpect_coord`
(`E_{S∼D^m}[g (S i)] = E_D[g]`), the **key block** of the unbiased estimator. It
expresses that marginalizing one coordinate of a product `D^m` gives back `D`. Proof:
we "carry" `g` onto coordinate `i` via `g' j x = w x · (if j = i then g x else 1)`,
so that `∏_j g' j (S j) = (∏_j w (S j)) · g (S i)`
(`Finset.prod_mul_distrib` splits, `prod_eq_single_of_mem` reduces the product of
`if`s to its single non-trivial term). The **product of sums** `Fintype.prod_sum`
(namespace `Fintype`, not `Finset` — the two `prod_sum` coexist) then gives
`∑_S ∏_j g' j (S j) = ∏_j ∑_x g' j x`, and this product equals
`(∑_x w·g) · (∑_x w)^{n−1} = E_D[g] · 1` (`D.sum_one`).

## This deliverable — unbiased estimator (brick 2c/3)

We prove the **unbiased estimator** `sampleExpect_empError_eq_trueError`
(`E_{S∼D^m}[empError f h S] = trueError D f h`): the empirical error, averaged over
i.i.d. draws, coincides with the true error (it is **centered** on it).
This is the second pillar of Hoeffding concentration. Proof: `empError S =
n⁻¹ · (∑_i ind(S_i))` (`ind = 1_{h≠f}`); pull out the scalar (`sampleExpect_smul`),
distribute the sum (`sampleExpect_sum`), then each indicator marginalizes to
`E_D[ind] = trueError` via `sampleExpect_coord` + `trueError_eq_expect`;
`∑_i trueError = n · trueError` (`sum_const`), and `field_simp` cancels `n⁻¹·n`.

## Remaining bricks — OPEN (documented as future work, no stub)

- **Hoeffding-for-Bernoulli**: `ℙ_S [ |empError − trueError| ≥ ε ] ≤
  2·exp(−2nε²)` (Chernoff method: Markov on `exp(t·(X̄−μ))` + `log t ≤ t−1`).
- **Final bound** `pac_finite_class_bound` (brick 3/3, union bound over finite `H`).

These bricks follow in dedicated iterations. We stay in the
**pedagogical ℝ-weight style** (no `ℝ≥0∞` / `Measure`).

English mirror of `PacLearning/SampleExpect.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): namespace
`PacLearning_en` (anti-collision with the FR `PacLearning` namespace); cross-module
`_en` imports `_en` (imports `PacLearning.Data_en` + `PacLearning.Sample_en` +
`PacLearning.Concentration_en`, pattern Perceptron_en #5683 / Gittins_en);
non-docstring proof code unchanged.
-/


namespace PacLearning_en

open Finset

variable {X : Type*} [Fintype X]
variable (D : Distribution X)

/-- **Empirical expectation** of `g : (Fin n → X) → ℝ` under the product distribution
`D^m`: weighted sum `∑ S, sampleWeight D S · g S`. This is the extension of `expect`
(over `X`) to the sample space. -/
noncomputable def sampleExpect {n : ℕ} (g : (Fin n → X) → ℝ) : ℝ :=
  ∑ S : Fin n → X, sampleWeight D S * g S

variable {D}

/-- The empirical expectation of a non-negative function is non-negative: a sum of
non-negative weights (`sampleWeight ≥ 0`) times `g ≥ 0`. -/
theorem sampleExpect_nonneg {n : ℕ} {g : (Fin n → X) → ℝ} (hg : ∀ S, 0 ≤ g S) :
    0 ≤ sampleExpect D g := by
  dsimp only [sampleExpect]
  apply sum_nonneg
  intro S _
  exact mul_nonneg (sampleWeight_nonneg (D := D) S) (hg S)

/-- The empirical expectation is linear in `g`: `E[a·g₁ + b·g₂] = a·E[g₁] + b·E[g₂]`
(since `∑` is). The factor `a` (resp. `b`) is moved to the left in each weighted
scalar product, then `← mul_sum` pulls it out of the sum. -/
theorem sampleExpect_linear {n : ℕ} {g₁ g₂ : (Fin n → X) → ℝ} (a b : ℝ) :
    sampleExpect D (fun S ↦ a * g₁ S + b * g₂ S) =
      a * sampleExpect D g₁ + b * sampleExpect D g₂ := by
  dsimp only [sampleExpect]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [show ∀ S, sampleWeight D S * (a * g₁ S) = a * (sampleWeight D S * g₁ S) from
               fun _ => by ring,
             show ∀ S, sampleWeight D S * (b * g₂ S) = b * (sampleWeight D S * g₂ S) from
               fun _ => by ring]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- **Normalization**: the empirical expectation of the constant function `c` is
`c` (the total mass of the samples is `1` by `sampleWeight_sum_one`).
This is the fact that `D^m` is a probability distribution, transposed to
expectations. -/
theorem sampleExpect_const (n : ℕ) (c : ℝ) :
    sampleExpect D (fun _ : Fin n → X ↦ c) = c := by
  dsimp only [sampleExpect]
  rw [← Finset.sum_mul, sampleWeight_sum_one n, one_mul]

/-- **Monotonicity** of the empirical expectation: if `g ≤ g'` pointwise, then
`E[g] ≤ E[g']` (weighted sum with non-negative weights). -/
theorem sampleExpect_mono {n : ℕ} {g g' : (Fin n → X) → ℝ}
    (h : ∀ S, g S ≤ g' S) : sampleExpect D g ≤ sampleExpect D g' := by
  dsimp only [sampleExpect]
  apply sum_le_sum
  intro S _
  exact mul_le_mul_of_nonneg_left (h S) (sampleWeight_nonneg (D := D) S)

/-- **Marginalization of a coordinate**: the expectation (under the product `D^m`)
of a function `g` depending only on a single coordinate `S i` equals its expectation
(under `D`). This is the **key block of the unbiased estimator**: it expresses that
marginalizing one coordinate of a product `D^m` gives back `D`.

Proof: we "carry" `g` onto coordinate `i` via `g' j x = w x · (if j = i
then g x else 1)`, so that `∏_j g' j (S j) = (∏_j w (S j)) · g (S i)` (the product
of the `if`s keeps only the term `j = i`). The Mathlib lemma `Finset.prod_sum`
then gives `∑_S ∏_j g' j (S j) = ∏_j ∑_x g' j x`, and this product equals
`(∑_x w·g) · (∑_x w)^{n−1} = E_D[g] · 1`. -/
theorem sampleExpect_coord {n : ℕ} (g : X → ℝ) (i : Fin n) :
    sampleExpect D (fun S : Fin n → X ↦ g (S i)) = expect D g := by
  dsimp only [sampleExpect, sampleWeight]
  -- `g'` carries `g` onto coordinate `i`, elsewhere the neutral factor `1`.
  let g' : Fin n → X → ℝ := fun j x ↦ D.weight x * (if j = i then g x else 1)
  -- (1) `∏_j g' j (S j) = (∏_j w (S j)) * g (S i)`: `prod_mul_distrib` splits the
  -- two factors, then `prod_eq_single_of_mem` reduces the product of the `if`s
  -- (a single non-trivial term at `j = i`) to `g (S i)`.
  have hprod : ∀ S : Fin n → X, ∏ j, g' j (S j) = (∏ j, D.weight (S j)) * g (S i) := by
    intro S
    simp only [g', Finset.prod_mul_distrib]
    rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ _) (fun b _ hb ↦ if_neg hb),
        if_pos rfl]
  -- (2) The summand `(∏_j w (S j)) * g (S i)` coincides pointwise with `∏_j g' j (S j)`.
  rw [Finset.sum_congr rfl (fun S _ ↦ (hprod S).symm)]
  -- (3) Product of sums = sum of products (`Fintype.prod_sum`, namespace `Fintype`)
  --: `∑_S ∏_j g' j (S j) = ∏_j ∑_x g' j x`.
  rw [← Fintype.prod_sum (κ := fun _ : Fin n ↦ X) g']
  -- (4) `∑_x g' j x`: `j = i` ⟹ `E_D[g]` (`∑ w·g`), else ⟹ `∑ w = 1` (`D.sum_one`).
  have hsum : ∀ j, ∑ x, g' j x = if j = i then expect D g else 1 := by
    intro j
    by_cases hj : j = i
    · simp only [g', expect, if_pos hj]
    · simp only [g', if_neg hj, mul_one, D.sum_one]
  simp only [hsum]
  -- (5) `∏_j (if j = i then expect D g else 1) = expect D g`: a single non-trivial term.
  rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ _) (fun b _ hb ↦ if_neg hb),
      if_pos rfl]

/-- **Factorization of a product (i.i.d. independence)**: the expectation (under the
product `D^m`) of a function of the form `∏_i h (S i)` — a product of one-coordinate
functions, i.i.d. by construction of the product distribution `D^m` — factorizes
into the product of expectations `∏_i E_D[h]`. This is **brick 3/5 of Hoeffding**
(product independence): for `h = exp(t · ind)`, it gives
`E_S[exp(t · ∑_i ind(S_i))] = E_S[∏_i exp(t·ind(S_i))] = ∏_i E_D[exp(t·ind)]`,
i.e. the **MGF of a sum = product of MGFs** — a key ingredient of Hoeffding's
two-sided concentration.

Proof: same skeleton as `sampleExpect_coord` — we carry `h` onto each coordinate
via `g' j x = w x · h x`, so that
`∏_j g' j (S j) = (∏_j w (S j)) · (∏_j h (S j))` (`Finset.prod_mul_distrib`),
then `Fintype.prod_sum` swaps product-of-sums and sum-of-products:
`∑_S ∏_j g' j (S j) = ∏_j ∑_x g' j x = ∏_j E_D[h]`. Simpler than
`sampleExpect_coord`: no `if` (every coordinate carries `h`), hence no
`Finset.prod_eq_single_of_mem` reduction. -/
theorem sampleExpect_prod_coord {n : ℕ} (h : X → ℝ) :
    sampleExpect D (fun S : Fin n → X ↦ ∏ i, h (S i)) = ∏ _ : Fin n, expect D h := by
  dsimp only [sampleExpect, sampleWeight]
  -- `g'` carries `h` onto each coordinate: `g' j x = w x · h x`.
  let g' : Fin n → X → ℝ := fun j x ↦ D.weight x * h x
  -- (1) `∏_j g' j (S j) = (∏_j w (S j)) * ∏_j h (S j)`: `prod_mul_distrib` splits.
  have hprod : ∀ S : Fin n → X,
      ∏ j, g' j (S j) = (∏ j, D.weight (S j)) * ∏ j, h (S j) := by
    intro S
    simp only [g', Finset.prod_mul_distrib]
  -- (2) The summand `(∏_j w (S j)) * ∏_j h (S j)` coincides pointwise with `∏_j g' j (S j)`.
  rw [Finset.sum_congr rfl (fun S _ ↦ (hprod S).symm)]
  -- (3) Product of sums = sum of products (`Fintype.prod_sum`):
  -- `∑_S ∏_j g' j (S j) = ∏_j ∑_x g' j x`.
  rw [← Fintype.prod_sum (κ := fun _ : Fin n ↦ X) g']
  -- (4) `∑_x g' j x = ∑_x w x · h x = E_D[h]` (independent of `j`).
  have hsum : ∀ j, ∑ x, g' j x = expect D h := by
    intro j
    simp only [g', expect]
  simp only [hsum]

/-- **Linearity over an indexed sum**: the empirical expectation of a sum of
functions is the sum of expectations (discrete Fubini: `∑_S w S · (∑_i F i S) =
∑_i ∑_S w S · F i S` via `Finset.mul_sum` then `Finset.sum_comm`). Reused by the
unbiased estimator `sampleExpect_empError_eq_trueError`. -/
theorem sampleExpect_sum {ι : Type*} [Fintype ι] {n : ℕ} (F : ι → ((Fin n → X) → ℝ)) :
    sampleExpect D (fun S ↦ ∑ i, F i S) = ∑ i, sampleExpect D (F i) := by
  dsimp only [sampleExpect]
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- **Linearity over a scalar factor**: `E[c · g] = c · E[g]` (the scalar is pulled
out of the weighted sum via `Finset.mul_sum`). Reused by the unbiased estimator
(to pull out the `1/n` factor of the empirical error). -/
theorem sampleExpect_smul {n : ℕ} (c : ℝ) (g : (Fin n → X) → ℝ) :
    sampleExpect D (fun S ↦ c * g S) = c * sampleExpect D g := by
  dsimp only [sampleExpect]
  simp only [show ∀ S, sampleWeight D S * (c * g S) = c * (sampleWeight D S * g S) from
               fun _ ↦ by ring]
  rw [← Finset.mul_sum]

/-- **Unbiased estimator**: the expectation (under `D^m`) of the empirical error
equals the true error. This is the fact that `empError` is an **unbiased** estimator
of `trueError`: averaged over draws `S ∼ D^m`, the empirical error coincides with
the true error (it is **centered** on `trueError`).

Proof: `empError S = (∑_i 1_{h(S_i)≠f(S_i)}) / n = n⁻¹ · (∑_i ind (S i))`. By
`sampleExpect_smul` (pull out `n⁻¹`), `sampleExpect_sum` (linearity), then
`sampleExpect_coord` (each indicator marginalizes to `E_D[ind] = trueError` via
`trueError_eq_expect`), we get
`E_S[empError] = n⁻¹ · (∑_i trueError) = n⁻¹ · (n · trueError) = trueError`. -/
theorem sampleExpect_empError_eq_trueError {n : ℕ} (f h : Hypothesis X) (hn : 0 < n) :
    sampleExpect D (fun S : Fin n → X ↦ empError f h S) = trueError D f h := by
  -- Misclassification indicator of an instance.
  let ind : X → ℝ := fun x ↦ if h x ≠ f x then 1 else 0
  -- (1) `empError f h S = (n:ℝ)⁻¹ · (∑ i, ind (S i))` (rewrite of the `1/n`).
  have h_emp : ∀ S : Fin n → X,
      empError f h S = (n : ℝ)⁻¹ * (∑ i : Fin n, ind (S i)) := by
    intro S
    dsimp only [empError, ind]
    field_simp
  -- (2) Per-coordinate marginal: `E_S[ind (S i)] = E_D[ind]` (sampleExpect_coord,
  -- D implicit → named arg `(D := D)` since D appears only in the goal).
  have h_coord : ∀ i : Fin n, sampleExpect D (fun S ↦ ind (S i)) = expect D ind := by
    intro i
    exact sampleExpect_coord (D := D) ind i
  -- (3) `expect D ind = trueError D f h`.
  have h_true : expect D ind = trueError D f h := (trueError_eq_expect (D := D) f h).symm
  -- (4) `n > 0` (in ℝ) for the final field_simp.
  have hnreal : (0 : ℝ) < n := mod_cast hn
  calc sampleExpect D (fun S : Fin n → X ↦ empError f h S)
      = sampleExpect D (fun S ↦ (n : ℝ)⁻¹ * (∑ i : Fin n, ind (S i))) := by
          simp only [h_emp]
    _ = (n : ℝ)⁻¹ * sampleExpect D (fun S ↦ ∑ i : Fin n, ind (S i)) := by
          rw [sampleExpect_smul]
    _ = (n : ℝ)⁻¹ * ∑ i : Fin n, sampleExpect D (fun S ↦ ind (S i)) := by
          rw [sampleExpect_sum]
    _ = (n : ℝ)⁻¹ * ∑ i : Fin n, expect D ind := by
          congr 1
          exact Finset.sum_congr rfl (fun i _ ↦ h_coord i)
    _ = (n : ℝ)⁻¹ * ∑ i : Fin n, trueError D f h := by rw [h_true]
    _ = (n : ℝ)⁻¹ * (n * trueError D f h) := by
          congr 1
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = trueError D f h := by
          field_simp

end PacLearning_en

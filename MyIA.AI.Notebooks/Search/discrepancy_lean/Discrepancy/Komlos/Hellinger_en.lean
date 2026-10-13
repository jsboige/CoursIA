/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

The original Dahia source lives in `gdahia/Komlos` (module
`Komlos/Hellinger.lean`, toolchain v4.34.0, `Finsupp` framework over
`E → ₀ ℝ`). The adaptation below follows the lake convention established
by k1.1 (`ShiftDistance.lean`) and k1.3 (`Overlap.lean`) : **explicit
Finset** framework.

**What the encoding barrier does not touch.** The analytic core of Dahia's
`tvDist_sq_le` — "for two weights `p`, `q` of unit `L²` norm, the total
variation distance between `p ^ 2` and `q ^ 2` is bounded by the `L²`
distance between `p` and `q`" — is stated **entirely on the weights**
`p q : ι → ℝ` and a finite sum. Neither `Finsupp`, nor `IsDist`, nor the
representation of the distributions enters it : only the rewriting
`tvDist P Q = 2⁻¹ * Σ |P x − Q x|` (`tvDist_eq_sum` in Dahia) consumes the
support. We therefore state the bound directly on the weights, with the
factor `2⁻¹` **explicit** — which is exactly what `Komlos.Cube` consumes
after setting `P = p ^ 2`, `Q = q ^ 2` and writing the shift distance as a
half-sum of absolute values. The brick is thus portable **before** the
distribution encoding choice (a : functions + `Finset`, b : verbatim
`Finsupp`) is settled, and remains valid under either.

**Scope of this commit** (brick k4.1, `lake build SUCCESS` required, 0
`sorry`) :

Bricks closed : `sum_sub_sq_eq` (for `p`, `q` of unit `L²` norm, the sum of
squared deviations equals `2 − 2⟨p, q⟩` — the rewriting the Cauchy–Schwarz
bound needs), `half_sum_abs_sq_sub_sq_sq_le` (the **Hellinger bound** :
`(½ Σ |p² − q²|)² ≤ Σ (p − q)²`, via Cauchy–Schwarz
`sum_mul_sq_le_sq_mul_sq` and `Σ (p + q)² ≤ 4`), `one_sub_sum_le_prod` (the
**Weierstrass product inequality** `1 − Σ a ≤ Π (1 − a)` on `[0, 1]`, via
`prod_one_sub_ordered`).

**Postponed to k4.2** : the "distribution" version of the bound — replacing
the weights by the distributions and the factor `2⁻¹` by
`tvDistance S P Q` in Finset vocabulary — as soon as `Komlos.Cube` fixes
its call site ; then the chain `Cube` → `NearInvariant` (Lemma 1.5), whose
`Transport` substrate is under arbitration (#19081). The detailed state
lives in `FORMAL_STATUS.md`.
-/

import Discrepancy.Basic

/-!
# Hellinger's inequality and Weierstrass' product inequality

Two analytic bricks of the Karingula–Lovett distillation.

`sum_sub_sq_eq` : for weights `p`, `q` of unit `L²` norm on a finite support
`s`, the sum of squared deviations equals `2 − 2 Σ p i * q i`. This is the
expanded form of the squared Euclidean distance, and the identity that
reduces the Hellinger bound to a Cauchy–Schwarz inequality.

`half_sum_abs_sq_sub_sq_sq_le` : the **Hellinger bound**. For weights `p`,
`q` of unit `L²` norm, the half-sum of absolute values of squared
deviations — that is, the total variation between the distributions
`p ^ 2` and `q ^ 2` — satisfies

  `(½ Σ |p i ^ 2 − q i ^ 2|) ^ 2 ≤ Σ (p i − q i) ^ 2`.

Proof : `|p² − q²| = |p + q| * |p − q|`, then Cauchy–Schwarz
`(Σ a b)² ≤ (Σ a²)(Σ b²)` with `a = |p + q|`, `b = |p − q|`, and finally
`Σ (p + q)² ≤ 2 (Σ p² + Σ q²) = 4`. The factor `2⁻¹` becomes `4⁻¹` after
squaring, whence the inequality.

`one_sub_sum_le_prod` : the **Weierstrass product inequality**
`1 − Σ a ≤ Π (1 − a)` for `a` valued in `[0, 1]`. This is the brick that
compares product distributions in `Komlos.Cube`.
-/

namespace Discrepancy.Komlos_en

open Finset

variable {ι : Type*}

/-- For weights `p`, `q` of unit `L²` norm on `s`, the sum of squared
deviations equals `2 − 2 Σ p i * q i`.

This is the identity `Σ (p − q)² = Σ p² − 2 Σ p q + Σ q²` closed by the two
norm hypotheses. It serves to reduce any bound on `Σ (p − q)²` to a bound on
the scalar product `Σ p i * q i`. -/
lemma sum_sub_sq_eq {s : Finset ι} {p q : ι → ℝ}
    (hp : ∑ i ∈ s, p i ^ 2 = 1) (hq : ∑ i ∈ s, q i ^ 2 = 1) :
    ∑ i ∈ s, (p i - q i) ^ 2 = 2 - 2 * ∑ i ∈ s, p i * q i := by
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, hp, hq, mul_assoc, ← mul_sum]
  ring

/-- **Hellinger bound.** For weights `p`, `q` of unit `L²` norm, the total
variation between the distributions `p ^ 2` and `q ^ 2` — written as the
half-sum of absolute values of squared deviations — is bounded by the `L²`
distance between the weights :

  `(2⁻¹ Σ |p i ^ 2 − q i ^ 2|) ^ 2 ≤ Σ (p i − q i) ^ 2`.

This is the brick `Komlos.Cube` consumes to bound the shift distance
between product distributions : the `p`, `q` there are the factor weights,
normalised by `sum_gridF_sq`. -/
lemma half_sum_abs_sq_sub_sq_sq_le {s : Finset ι} {p q : ι → ℝ}
    (hp : ∑ i ∈ s, p i ^ 2 = 1) (hq : ∑ i ∈ s, q i ^ 2 = 1) :
    ((2⁻¹ : ℝ) * ∑ i ∈ s, |p i ^ 2 - q i ^ 2|) ^ 2
      ≤ ∑ i ∈ s, (p i - q i) ^ 2 := by
  have hfact : ∑ i ∈ s, |p i ^ 2 - q i ^ 2|
      = ∑ i ∈ s, |p i + q i| * |p i - q i| := by
    refine sum_congr rfl ?_
    intro x _
    rw [sq_sub_sq, abs_mul]
  rw [hfact, mul_pow, inv_pow, inv_mul_le_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 2)]
  refine (sum_mul_sq_le_sq_mul_sq s (fun x => |p x + q x|)
    (fun x => |p x - q x|)).trans ?_
  simp only [sq_abs]
  refine mul_le_mul_of_nonneg_right ?_ ?_
  · refine (sum_le_sum (g := fun x => 2 * (p x ^ 2 + q x ^ 2)) ?_).trans_eq ?_
    · intro x _
      exact add_sq_le
    · rw [← mul_sum, sum_add_distrib, hp, hq]
      norm_num
  · refine sum_nonneg ?_
    intro x _
    exact sq_nonneg _

/-- **Weierstrass product inequality.** For `a` valued in `[0, 1]` on `s`,
we have `1 − Σ a ≤ Π (1 − a)`.

This is the brick that bounds a product of factors below by the sum of their
defects : it turns an additive bound (a sum of "small perturbations") into a
multiplicative bound on the product distribution. -/
lemma one_sub_sum_le_prod [LinearOrder ι] (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  rw [prod_one_sub_ordered]
  gcongr with i hi
  refine mul_le_of_le_one_right (h0 i hi) ?_
  have hle : ∏ j ∈ s.filter (fun j => j < i), (1 - a j)
      ≤ ∏ _j ∈ s.filter (fun j => j < i), (1 : ℝ) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro j hj
      exact sub_nonneg.mpr (h1 j (mem_filter.1 hj).1)
    · intro j hj
      exact sub_le_self _ (h0 j (mem_filter.1 hj).1)
  simpa using hle

end Discrepancy.Komlos_en

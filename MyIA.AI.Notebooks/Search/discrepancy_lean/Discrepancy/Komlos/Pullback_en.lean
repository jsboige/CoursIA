/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the repository `gdahia/Komlos` (module
`Komlos/Pullback.lean`, toolchain v4.34.0, `Finsupp` framework over `E →₀ ℝ`).
The adaptation takes the module over **name for name**, but first delivers only
its **convexity-free** part — see the scope below.

**Scope of this commit** (brick k2.1, `lake build SUCCESS` required, 0 `sorry`) :

The **pullback step** of Lemma 1.4 decomposes, in Dahia, into three lemmas :
`exists_sign_mul_add_eq` (real arithmetic), `add_smul_mem_convexHull` (convex
hull of a segment) and `pullback` (the full step). The last two **consume
`convexHull`**, which this lake imports nowhere (`convexHull` : 0 occurrence
before this module). This brick therefore delivers the **three ingredients that
do not depend on it**, so that the convexity surface opens on an
already-verified base :

- `exists_sign_mul_add_eq` — the **arithmetic key** : for `β ≥ 1/3` and
  `|a| ≤ 1 − β`, there is a sign `e ∈ {±1}` and a coefficient `c` with
  `|c| ≤ 1` such that `c·β + a = e/3`. This is what produces the sign `ε` of
  k2's conclusion ;
- `segment_repr` — the **segment identity** : any point `x + c·v` with
  `|c| ≤ 1` writes as a convex combination of `x − v` and `x + v`, with weights
  `(1 − c)/2` and `(1 + c)/2`. This is the algebra `add_smul_mem_convexHull`
  wraps in Dahia, but **the algebra alone**, without `convexHull` ;
- `sum_mul_add_split` — the **weighted linearity** consumed by the computation
  of `pullback` : the sum `Σ R y · (h y · c + g y)` splits into
  `c · (Σ R y · h y) + Σ R y · g y`. It is the only sum manipulation of the
  pullback step that is not convexity.

**Deferred to k2.2** (convexity surface) : `add_smul_mem_convexHull` and
`pullback` — the only two lemmas of the Dahia module that require
`convexHull ℝ`. The detailed state lives in `FORMAL_STATUS.md`.
-/

import Discrepancy.Basic_en

/-!
# Algebra of the pullback step (Lemma 1.4, Karingula–Lovett)

Lemma 1.4 concludes `μ(P) + Σ ε_i v_i ∈ conv(supp P)`. Its induction step splits
in the direction of the last vector, applies the induction hypothesis in the
product space, then **brings back** the resulting point into `conv(supp P)` :
that is the *pullback*. This module delivers the algebra of that step,
independently of any notion of convex hull.

**Why separate.** Opening `convexHull` in this lake is a structural gesture
(first convex-analysis surface of the lake) ; mixing it with real arithmetic and
sum manipulation would make the diagnosis of a build failure ambiguous.
Delivered separately, the three lemmas below are verifiable **without**
`convexHull`, and the next brick brings only one new ingredient.

**Scope of the result.** `exists_sign_mul_add_eq` is the ingredient that
produces the **signed conclusion** : `e ∈ {±1}` is the sign `ε` of k2's
conclusion, and the bound `|c| ≤ 1` is what allows reading `x + c·v` as a point
of the segment `[x − v, x + v]` — hence `segment_repr`, which makes that
reading explicit. Both lemmas are stated over `ℝ` (no base required) ; only
`segment_repr` needs an abelian group carrying a real module structure, i.e.
the minimal framework in which the statement makes sense.
-/

namespace Discrepancy.Komlos_en

/-- **Arithmetic key of the pullback.** If `β ≥ 1/3` and `|a| ≤ 1 − β`, there
is a sign `e ∈ {±1}` and a coefficient `c` such that `|c| ≤ 1` and
`c * β + a = e / 3`.

This is Dahia's `exists_sign_mul_add_eq` (`Komlos/Pullback.lean`), transposed
verbatim : the statement bears on `ℝ` only, no base structure is required. The
sign `e` is the sign `ε` of Lemma 1.4's conclusion ; the bound `|c| ≤ 1` is what
makes `x + c • v` a point of the segment `[x − v, x + v]` (cf `segment_repr`).

Proof : case analysis on the sign of `a`. For `a ≥ 0`, take `e = 1` and
`c = (1/3 − a) / β` ; the membership `|c| ≤ 1` reduces to `|1/3 − a| ≤ β`, which
`linarith` closes with `hβ` and `|a| ≤ 1 − β`. The case `a < 0` is symmetric
with `e = −1`. -/
lemma exists_sign_mul_add_eq {β a : ℝ} (hβ : 3⁻¹ ≤ β) (ha : |a| ≤ 1 - β) :
    ∃ e c : ℝ, (e = 1 ∨ e = -1) ∧ |c| ≤ 1 ∧ c * β + a = e / 3 := by
  have hβ0 : 0 < β := by linarith
  obtain ⟨ha₁, ha₂⟩ := abs_le.1 ha
  rcases le_total 0 a with h | h
  · refine ⟨1, (3⁻¹ - a) / β, by norm_num, ?_, by field_simp; ring⟩
    rw [abs_div, abs_of_pos hβ0, div_le_one hβ0, abs_le]
    constructor <;> linarith
  · refine ⟨-1, (-3⁻¹ - a) / β, by norm_num, ?_, by field_simp; ring⟩
    rw [abs_div, abs_of_pos hβ0, div_le_one hβ0, abs_le]
    constructor <;> linarith

/-- **Segment identity.** For `|c| ≤ 1`, the point `x + c • v` is the convex
combination of `x − v` and `x + v` with weights `(1 − c) / 2` and
`(1 + c) / 2` :

`((1 − c) / 2) • (x − v) + ((1 + c) / 2) • (x + v) = x + c • v`.

Both weights are nonnegative and sum to 1 as soon as `|c| ≤ 1` — precisely the
hypothesis `hc` of the lemma `add_smul_mem_convexHull` in Dahia, which wraps
this identity in `Convex.add_smul_sub_mem` **without** the convex-hull part
(that one stays with brick k2.2).

The direction of the weights is the one of the statement : `x − v` receives
`(1 − c) / 2` and `x + v` receives `(1 + c) / 2`, so that the coefficient of `v`
is `−(1 − c)/2 + (1 + c)/2 = c`. Swapping the two weights yields `x − c • v`,
not `x + c • v` — the exact mistake made and corrected while drafting this
lemma, recorded here because it is easy to repeat.

Proof : `module` (linearity of `•` and distributivity over `x ± v`). -/
lemma segment_repr {E : Type*} [AddCommGroup E] [Module ℝ E] (x v : E) (c : ℝ) :
    ((1 - c) / 2) • (x - v) + ((1 + c) / 2) • (x + v) = x + c • v := by
  module

/-- **Weighted linearity of a sum.** For a `Finset` `T` and functions
`R`, `h`, `g : ι → ℝ`,

`Σ y ∈ T, R y * (h y * c + g y) = c * (Σ y ∈ T, R y * h y) + Σ y ∈ T, R y * g y`.

This is the sum manipulation of Dahia's `pullback` computation — `mul_sub`,
`sum_sub_distrib`, `mul_sum` — extracted in its reusable form. It depends on
neither the base nor convexity.

Proof : distributivity (`mul_add`), additivity of the sum
(`Finset.sum_add_distrib`), then extraction of the constant factor `c`
(`Finset.mul_sum`) and commutativity. -/
lemma sum_mul_add_split {ι : Type*} (T : Finset ι) (R h g : ι → ℝ) (c : ℝ) :
    ∑ y ∈ T, R y * (h y * c + g y)
      = c * (∑ y ∈ T, R y * h y) + ∑ y ∈ T, R y * g y := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

end Discrepancy.Komlos_en

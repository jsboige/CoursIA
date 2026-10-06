/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted for `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979): toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the `gdahia/Komlos` repository (module
`Komlos/SignedSums.lean`, toolchain v4.34.0, `Finsupp` framework over
`E →₀ ℝ`). The final assembly — the `induction n with` iteration of
Lemma 1.4 — reads there at l.37-58. This lake module opens the
distillation: the first brick `sum_smul_inl` ships here in generic form,
the consumption map of the organs is measured at the top of the module,
and the framework decision (option (c), arbitrated in k2.6a) is recorded.
-/

import Discrepancy.Basic_en

/-!
# Signed sums — assembly of Lemma 1.4 (brick k2.6)

The goal of this module is the final assembly of the elementary route
(Karingula–Lovett): the `induction n with` iteration of the
`gdahia/Komlos` oracle (`SignedSums.lean` l.37-58), which consumes
`mean_mem_convexHull` in the base case (l.42), `mean_split` +
`sum_smul_inl` in the step (l.53), and `pullback` in the closing (l.55).

## Genericity map (measured on 2026-10-06, k2.5 tip 87b4f35871)

The oracle's induction re-instantiates its organs at every level on a
growing ambient `E → E × ℝ → (E × ℝ) × ℝ → …` — it is the generality of
`E` that absorbs the growth. The lake's k2.0–k2.5 organs are monomorphic
(`Fin d → ℤ`, height `Bool`):

| Oracle organ | Our lake | Status |
|---|---|---|
| `split : (E →₀ ℝ) → (E × ℝ →₀ ℝ)` | `Split.split` (`Fin d → ℤ`, `× Bool`) | monomorphic |
| `mean_split` (barycenter preserved) | `MeanSplit.mean_split_of_support` | monomorphic |
| `shiftDist_split_le` | acquired k1.6 | monomorphic |
| `splitBit_eq` | `SplitBit` | monomorphic |
| `pullback` (generic) | `Pullback.pullback` (`toReal`/`toRealProd`) | monomorphic |
| `mean_mem_convexHull` | `Distribution.mean_mem_convexHull` (k2.5) | monomorphic |
| `sum_smul_inl` | **missing — shipped below, generic** | ✓ k2.6 |
| convexHull (`add_smul`/`sum_smul`/`mem_convexHull'`) | `Pullback` l.150/189/213 | ✓ generic |

The architectural gap is **arbitrated in k2.6a** (option (c): the growing
space is realized as `Fin (d + k) → ℤ` via the `liftUp` embedding,
without re-generalizing the organs — route α is set aside, route β
(two-space ping-pong) is closed by measurement). `sum_smul_inl` remains
the generic ℝ-modular organ, **complementary to `sum_smul_snoc`**
(k2.6a, lake form on the grid side): consumable on the transport/hull
side, where the moments live in `ℝ`.
-/

namespace Discrepancy.Komlos_en

/-- The left component of a sum of vectors `ε i • (v i, 0)` is the sum
of the left components — the `Finset` counterpart of the oracle's
`sum_smul_inl` (`split.lean` l.50), used by the rewrite `rw [mean_split,
sum_smul_inl, …]` of the inductive step. Generic in `E`: it is the only
organ of the step the lake did not have, and it does not depend on the
grid. -/
lemma sum_smul_inl {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ε : Fin n → ℝ) (v : Fin n → E) :
    (∑ i, ε i • (v i, (0 : ℝ))) = (∑ i, ε i • v i, (0 : ℝ)) := by
  refine Prod.ext ?_ ?_ <;> simp [Prod.smul_mk, Prod.fst_sum, Prod.snd_sum]

end Discrepancy.Komlos_en

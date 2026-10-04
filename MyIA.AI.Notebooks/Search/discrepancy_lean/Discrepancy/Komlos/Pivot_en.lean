/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

The original Dahia source lives in `gdahia/Komlos` (module
`Komlos/ShiftDistance.lean`, toolchain v4.34.0, `Finsupp` framework over
`E →₀ ℝ`). The adaptation below follows the lake convention established
by brick k1.1 (`ShiftDistance.lean`) : **explicit Finset** framework
`P : (Fin d → ℤ) → ℝ` with the support `S` passed as an argument.

**Scope of this commit** (brick k1.4, `lake build SUCCESS` required, 0
`sorry`) :

Bricks closed : the **pivot identity**
`overlap_translate_eq_one_sub_shiftDistance` — for a mass-1 distribution on
a support invariant under `u`, the overlap of `P` with its translate is
exactly `1 − Δ(P, u)` — and its symmetric form
`shiftDistance_eq_one_sub_overlap` (`shiftDist_eq_one_sub_overlap` in
Dahia). The proof telescopes the pointwise identity
`min = ½(a + b − |a − b|)` from k1.3, the re-indexing `sum_translate_image`
from k1.2 (both masses equal 1) and the distributivity of sums — it is the
hinge connecting bricks k1.1 through k1.3 into a single equation.

**Postponed to k1.5** : `overlap_tr` (invariance of the overlap under a
common translation, same re-indexing path) ; Claim 3.2
(`Δ(T_v P, (u, 0)) ≤ Δ(P, u)`, requires the k1.2 splitting through the
pivot) ; `split_tr` (splitting ∘ translation commutation). The detailed
state lives in `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.Split_en
import Discrepancy.Komlos.Overlap_en

/-!
# Pivot identity `overlap = 1 − Δ` (Karingula–Lovett)

This module connects the three upstream bricks : for a mass-1 `P` on a
support `S` invariant under translation by `u`, the overlap of `P` with its
translate by `u` is exactly `1 − shiftDistance S P u`. This is the equation
through which the elementary proof of Komlós carries geometric information
(the translation distance `Δ`) over to combinatorial information (the
preserved common mass), before controlling it through the splitting `split`
(k1.2).

The proof follows Dahia's `shiftDist_eq_one_sub_overlap` (`gdahia/Komlos`),
in the explicit Finset framework of the lake : the pointwise identity
`min_eq_half_add_sub_abs` (k1.3) is summed termwise, both masses are
brought to 1 through `sum_translate_image` (k1.2), and the arithmetic
closes by `ring`.
-/

namespace Discrepancy.Komlos_en

/-- **Pivot identity** : for a function `P` of mass 1 on a support `S`
invariant under translation by `u`, the overlap of `P` with its translate
is exactly `1 − Δ(P, u)` — the lake form of Dahia's
`shiftDist_eq_one_sub_overlap`, the hinge step between bricks k1.1
(distance) and k1.3 (overlap). -/
lemma overlap_translate_eq_one_sub_shiftDistance {d : ℕ} {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)} (hmass : ∑ x ∈ S, P x = 1) {u : Fin d → ℤ}
    (hS : S.image (fun x => x + u) = S) :
    overlap P (fun x => P (x + u)) S = 1 - shiftDistance S P u := by
  have htr : ∑ x ∈ S, P (x + u) = 1 := by
    rw [sum_translate_image u hS, hmass]
  have hmin : ∀ x ∈ S, min (P x) (P (x + u))
      = (1 / 2 : ℝ) * (P x + P (x + u) - |P (x + u) - P x|) := by
    intro x _
    rw [min_eq_half_add_sub_abs, abs_sub_comm]
  have hsum : ∑ x ∈ S, (P x + P (x + u) - |P (x + u) - P x|)
      = (∑ x ∈ S, P x) + (∑ x ∈ S, P (x + u)) - ∑ x ∈ S, |P (x + u) - P x| := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  unfold overlap shiftDistance
  rw [Finset.sum_congr rfl hmin, ← Finset.mul_sum, hsum, hmass, htr]
  ring

/-- Symmetric form of the pivot identity in Dahia's direction
(`shiftDist_eq_one_sub_overlap`) : the translation distance of a
distribution equals `1 −` its overlap with its translate. -/
lemma shiftDistance_eq_one_sub_overlap {d : ℕ} {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)} (hmass : ∑ x ∈ S, P x = 1) {u : Fin d → ℤ}
    (hS : S.image (fun x => x + u) = S) :
    shiftDistance S P u = 1 - overlap P (fun x => P (x + u)) S := by
  rw [overlap_translate_eq_one_sub_shiftDistance hmass hS]
  ring

end Discrepancy.Komlos_en

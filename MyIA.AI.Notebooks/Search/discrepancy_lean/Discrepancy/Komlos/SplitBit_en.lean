/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

The original Dahia source lives in `gdahia/Komlos` (module
`Komlos/Split.lean`, toolchain v4.34.0, `Finsupp` framework). The adaptation
below follows the lake convention established by brick k1.1
(`ShiftDistance.lean`) : **explicit Finset** framework with the support as
an argument, `Bool` height for the product space (k1.2).

**Scope of this commit** (brick k1.6, `lake build SUCCESS` required, 0
`sorry`) :

Bricks closed : `overlap_tr` (invariance of the overlap under a common
translation of both functions — the two-function case of the k1.2
re-indexing), `splitBit` (half the common mass of the two translates of
`P`, `splitBit` in Dahia), `sum_split_high` (the `splitBit` is the mass of
the high slice of the splitting) and `splitBit_eq`
(`splitBit = ½(1 − Δ(P, 2v))` — `splitBit_eq` in Dahia : a re-indexing by
`−v` brings the overlap of the two translates back to that of `P` with its
translate by `2v`, which the k1.4 pivot identity closes ; it is the
ingredient consumed by Lemma 1.4).

**Postponed to k2 (Lemma 1.4)** : `mean_split` (the mean of `T_v P` is
`(mean P, splitBit v P)`) and the entropy lemma. The detailed state lives
in `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.Overlap_en
import Discrepancy.Komlos.Pivot_en
import Discrepancy.Komlos.Split_en

/-!
# Translation invariance and the splitting bit (Karingula–Lovett)

This module closes two lateral dependencies of brick k1 : the invariance of
the overlap under a common translation of both functions (`overlap_tr`),
and the **splitting bit** `splitBit` — the mass of the high slice of
`T_v P`, written as half the common mass of the two translates of `P`.
The identity `splitBit_eq` (`½(1 − Δ(P, 2v))`) carries the information of
the splitting over to the translation distance : it is the ingredient of
Lemma 1.4 of Karingula–Lovett.
-/

namespace Discrepancy.Komlos_en

/-- Invariance of the overlap under a common translation of both functions :
`overlap (P∘(·+u)) (Q∘(·+u)) S = overlap P Q S` under invariance of the
support — the two-function case of `sum_translate_image` (k1.2), the summed
function being `(fun x => min (P x) (Q x)) ∘ (· + u)`. `overlap_tr` in
Dahia. -/
lemma overlap_tr {d : ℕ} {P Q : (Fin d → ℤ) → ℝ} {S : Finset (Fin d → ℤ)}
    {u : Fin d → ℤ} (hS : S.image (fun x => x + u) = S) :
    overlap (fun x => P (x + u)) (fun x => Q (x + u)) S = overlap P Q S := by
  unfold overlap
  dsimp only
  exact sum_translate_image u hS (P := fun x => min (P x) (Q x))

/-- **Splitting bit** : half the common mass of the two translates of `P`
(`splitBit` in Dahia) — it is the mass of the high slice of `T_v P`
(cf `sum_split_high`). -/
noncomputable def splitBit {d : ℕ} (v : Fin d → ℤ) (P : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) : ℝ :=
  (1 / 2 : ℝ) * overlap (fun x => P (x + v)) (fun x => P (x - v)) S

/-- The `splitBit` is the mass of the high slice of the splitting :
`∑ x ∈ S, split v P (x, true) = splitBit v P S`. -/
lemma sum_split_high {d : ℕ} (v : Fin d → ℤ) (P : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) :
    ∑ x ∈ S, split v P (x, true) = splitBit v P S := by
  have h : ∑ x ∈ S, split v P (x, true)
      = ∑ x ∈ S, (1 / 2 : ℝ) * min (P (x + v)) (P (x - v)) :=
    Finset.sum_congr rfl fun x _ => split_apply_one v P x
  unfold splitBit overlap
  rw [h, ← Finset.mul_sum]

/-- **Splitting bit identity** : `splitBit v P S = ½(1 − Δ(P, 2v))`
(`splitBit_eq` in Dahia). The re-indexing by `−v` brings the overlap of the
two translates back to that of `P` with its translate by `2v`, which the
pivot identity (k1.4) closes. -/
lemma splitBit_eq {d : ℕ} (v : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)} (hmass : ∑ x ∈ S, P x = 1)
    (hSv : S.image (fun x => x + v) = S)
    (hSvm : S.image (fun x => x - v) = S) :
    splitBit v P S = (1 / 2 : ℝ) * (1 - shiftDistance S P (v + v)) := by
  have hS2 : S.image (fun x => x + (v + v)) = S := by
    have hcomp : (fun x => x + (v + v)) = (fun x => x + v) ∘ (fun x => x + v) := by
      funext x
      show x + (v + v) = (x + v) + v
      abel
    rw [hcomp, ← Finset.image_image, hSv, hSv]
  have htr : overlap (fun x => P (x + v)) (fun x => P (x - v)) S
      = overlap P (fun x => P (x + (v + v))) S := by
    unfold overlap
    dsimp only
    rw [← sum_translate_image (-v) (P := fun x => min (P x) (P (x + (v + v)))) hSvm]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : x + -v + (v + v) = x + v := by abel
    rw [h1]
    exact min_comm _ _
  unfold splitBit
  rw [htr, overlap_translate_eq_one_sub_shiftDistance hmass hS2]

end Discrepancy.Komlos_en
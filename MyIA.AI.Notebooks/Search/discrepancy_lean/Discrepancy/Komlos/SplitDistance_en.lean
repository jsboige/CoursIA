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

**Scope of this commit** (brick k1.5, `lake build SUCCESS` required, 0
`sorry`) :

Bricks closed : `shiftDistanceProd` (translation distance on the product
space, translation on the first coordinate), `sum_prodSnd_image`
(re-indexing of the product sum under invariance of the product support),
`overlapProd` + `sum_le_overlap_prod` (overlap and lower bound on the
product space, transposed from k1.3),
`overlap_shiftProd_eq_one_sub_shiftDistanceProd` + corollary
`shiftDistanceProd_eq_one_sub_overlap` (the k1.4 pivot identity transposed
to the product space), `split_tr` (splitting ∘ translation commutation —
`split_tr` in Dahia), and **Claim 3.2** `shiftDistanceProd_split_le` :
splitting does not increase the translation distance in the directions
coming from the base (`shiftDist_split_le` in Dahia). The proof is the
direct port of Dahia's skeleton : pivot on both sides → `split_tr` →
lower bound through `sum_le_overlap` of the split of the pointwise minimum
(via `split_mass` and `split_mono`).

**Postponed to k1.6** : `overlap_tr` (invariance of the overlap under a
common translation) ; remaining `shiftDistance_*` identities. The detailed
state lives in `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.Split_en
import Discrepancy.Komlos.Overlap_en
import Discrepancy.Komlos.Pivot_en

/-!
# Translation–splitting compatibility : Claim 3.2 (Karingula–Lovett)

This module closes the hinge opened by the pivot identity (k1.4) : it
transposes the translation distance and the pivot to the **product space**
`(ℤ^d) × Bool` on which the splitting `T_v` lives (k1.2), proves that the
splitting commutes with translation (`split_tr`), and then establishes the
**Claim 3.2** of the paper : splitting a distribution cannot increase its
translation distance in the directions coming from the base —
`Δ(T_v P, (u, 0)) ≤ Δ(P, u)`.

This is the lake form of Dahia's `shiftDist_split_le` (`gdahia/Komlos`,
module `Komlos/Split.lean`) : both legs go through the pivot identity
(k1.4), `split_tr` identifies the translate of `T_v P` with `T_v` of the
translate of `P`, and the overlap inequality closes termwise through
`sum_le_overlap` (k1.3) on the split of the pointwise minimum
`min(P, P∘(·+u))` — which `split_mass` (k1.2) re-indexes and `split_mono`
(k1.2) lower-bounds.
-/

namespace Discrepancy.Komlos_en

/-- Translation distance on the product space `(ℤ^d) × Bool` : the
translation `u` acts on the first coordinate, the `Bool` height is
unchanged. This is the natural distance of `T_v P` (k1.2) and of its
translate `(u, 0)` in Claim 3.2. -/
noncomputable def shiftDistanceProd {d : ℕ}
    (T : Finset ((Fin d → ℤ) × Bool)) (Q : (Fin d → ℤ) × Bool → ℝ)
    (u : Fin d → ℤ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y ∈ T, |Q (y.1 + u, y.2) - Q y|

/-- Re-indexing of the product sum under invariance of the support by the
first-coordinate translation : `∑ Q ∘ (· + (u, 0)) = ∑ Q` — the product
case of `sum_invariance_image` (k1.2), the translation being injective. -/
lemma sum_prodSnd_image {d : ℕ} (u : Fin d → ℤ)
    {Q : (Fin d → ℤ) × Bool → ℝ} {T : Finset ((Fin d → ℤ) × Bool)}
    (hT : T.image (fun y => (y.1 + u, y.2)) = T) :
    ∑ y ∈ T, Q (y.1 + u, y.2) = ∑ y ∈ T, Q y := by
  have hinj : ∀ a ∈ T, ∀ b ∈ T, (a.1 + u, a.2) = (b.1 + u, b.2) → a = b := by
    intro a _ b _ hab
    rw [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    rw [Prod.mk.injEq]
    exact ⟨add_right_cancel h1, h2⟩
  calc ∑ y ∈ T, Q (y.1 + u, y.2)
      = ∑ z ∈ T.image (fun y => (y.1 + u, y.2)), Q z :=
        (Finset.sum_image hinj).symm
    _ = ∑ z ∈ T, Q z := by rw [hT]

/-- Overlap on the product space `(ℤ^d) × Bool` : transposed form of
`overlap` (k1.3), whose instance is fixed to the base `ℤ^d`. -/
noncomputable def overlapProd {d : ℕ} (Q R : (Fin d → ℤ) × Bool → ℝ)
    (T : Finset ((Fin d → ℤ) × Bool)) : ℝ := ∑ y ∈ T, min (Q y) (R y)

/-- Lower bound of a sum by the product overlap — transposed form of
`sum_le_overlap` (k1.3). -/
lemma sum_le_overlap_prod {d : ℕ} {R Q Q' : (Fin d → ℤ) × Bool → ℝ}
    {T : Finset ((Fin d → ℤ) × Bool)}
    (hRQ : ∀ y ∈ T, R y ≤ Q y) (hRQ' : ∀ y ∈ T, R y ≤ Q' y) :
    ∑ y ∈ T, R y ≤ overlapProd Q Q' T := by
  rw [overlapProd]
  exact Finset.sum_le_sum fun y hy => le_min (hRQ y hy) (hRQ' y hy)

/-- **Pivot identity on the product space** : the k1.4 form transposed to
`(ℤ^d) × Bool` — for `Q` of mass 1 on `T` invariant under the
first-coordinate translation, `overlap Q (Q ∘ (· + (u, 0))) = 1 − Δ(Q, u)`.
This is the leg that carries Claim 3.2 over to `T_v P`. -/
lemma overlap_shiftProd_eq_one_sub_shiftDistanceProd {d : ℕ}
    {Q : (Fin d → ℤ) × Bool → ℝ} {T : Finset ((Fin d → ℤ) × Bool)}
    (hmass : ∑ y ∈ T, Q y = 1) {u : Fin d → ℤ}
    (hT : T.image (fun y => (y.1 + u, y.2)) = T) :
    overlapProd Q (fun y => Q (y.1 + u, y.2)) T = 1 - shiftDistanceProd T Q u := by
  have htr : ∑ y ∈ T, Q (y.1 + u, y.2) = 1 := by
    rw [sum_prodSnd_image u hT, hmass]
  have hmin : ∀ y ∈ T, min (Q y) (Q (y.1 + u, y.2))
      = (1 / 2 : ℝ) * (Q y + Q (y.1 + u, y.2)
          - |Q (y.1 + u, y.2) - Q y|) := by
    intro y _
    rw [min_eq_half_add_sub_abs, abs_sub_comm]
  have hsum : ∑ y ∈ T, (Q y + Q (y.1 + u, y.2)
        - |Q (y.1 + u, y.2) - Q y|)
      = (∑ y ∈ T, Q y) + (∑ y ∈ T, Q (y.1 + u, y.2))
        - ∑ y ∈ T, |Q (y.1 + u, y.2) - Q y| := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  unfold overlapProd shiftDistanceProd
  rw [Finset.sum_congr rfl hmin, ← Finset.mul_sum, hsum, hmass, htr]
  ring

/-- Symmetric form of the product pivot : `Δ(Q, u) = 1 −` the overlap with
its translate — the k1.5 version of `shiftDistance_eq_one_sub_overlap`. -/
lemma shiftDistanceProd_eq_one_sub_overlap {d : ℕ}
    {Q : (Fin d → ℤ) × Bool → ℝ} {T : Finset ((Fin d → ℤ) × Bool)}
    (hmass : ∑ y ∈ T, Q y = 1) {u : Fin d → ℤ}
    (hT : T.image (fun y => (y.1 + u, y.2)) = T) :
    shiftDistanceProd T Q u = 1 - overlapProd Q (fun y => Q (y.1 + u, y.2)) T := by
  rw [overlap_shiftProd_eq_one_sub_shiftDistanceProd hmass hT]
  ring

/-- Splitting commutes with translation (`split_tr` in Dahia) :
`T_v (P ∘ (· + u)) = (T_v P) ∘ (· + (u, 0))` — the support point of
Claim 3.2, it identifies the translate of `T_v P` with `T_v` of the
translate of `P`. -/
lemma split_tr {d : ℕ} (v u : Fin d → ℤ) (P : (Fin d → ℤ) → ℝ) :
    split v (fun x => P (x + u)) = fun y => split v P (y.1 + u, y.2) := by
  funext y
  obtain ⟨x, b⟩ := y
  have h1 : x + v + u = x + u + v := by abel
  have h2 : x - v + u = x + u - v := by abel
  cases b with
  | false =>
    rw [split_apply_zero, split_apply_zero, h1, h2]
  | true =>
    rw [split_apply_one, split_apply_one, h1, h2]

/-- **Claim 3.2** (Karingula–Lovett) : splitting does not increase the
translation distance in the directions coming from the base —
`Δ(T_v P, (u, 0)) ≤ Δ(P, u)` under mass 1 and invariance of the support
under `u` and `±v`. Lake form of Dahia's `shiftDist_split_le` ; the proof
skeleton is its direct port (pivot on both sides, `split_tr`, then
`sum_le_overlap` on the split of the pointwise minimum re-indexed by
`split_mass`). -/
theorem shiftDistanceProd_split_le {d : ℕ} (v u : Fin d → ℤ)
    {P : (Fin d → ℤ) → ℝ} {S : Finset (Fin d → ℤ)}
    (hmass : ∑ x ∈ S, P x = 1)
    (hSu : S.image (fun x => x + u) = S)
    (hSv : S.image (fun x => x + v) = S)
    (hSvm : S.image (fun x => x - v) = S) :
    shiftDistanceProd (S ×ˢ (Finset.univ : Finset Bool)) (split v P) u
      ≤ shiftDistance S P u := by
  have hT : (S ×ˢ (Finset.univ : Finset Bool)).image
        (fun y => (y.1 + u, y.2)) = S ×ˢ (Finset.univ : Finset Bool) := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_image] at hy
      obtain ⟨⟨a, b⟩, hmem, heq⟩ := hy
      rw [Finset.mem_product] at hmem ⊢
      obtain ⟨ha, hb⟩ := hmem
      have h1 : a + u = y.1 := congrArg Prod.fst heq
      have h2 : b = y.2 := congrArg Prod.snd heq
      rw [← h1, ← h2]
      exact ⟨by rw [← hSu]; exact Finset.mem_image_of_mem _ ha, hb⟩
    · intro hy
      rw [Finset.mem_product] at hy
      obtain ⟨hc, hb⟩ := hy
      have hc' : y.1 ∈ S.image (fun x => x + u) := by rw [hSu]; exact hc
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hc'
      exact Finset.mem_image.mpr
        ⟨(a, y.2), by rw [Finset.mem_product]; exact ⟨ha, hb⟩, by rw [hae]⟩
  have hmassT : ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool), split v P y = 1 := by
    rw [split_mass v hSv hSvm, hmass]
  have hmassTr : ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool),
      split v P (y.1 + u, y.2) = 1 := by
    rw [sum_prodSnd_image u hT, hmassT]
  rw [shiftDistanceProd_eq_one_sub_overlap hmassT hT,
    shiftDistance_eq_one_sub_overlap hmass hSu, ← split_tr v u P,
    sub_le_sub_iff_left]
  calc overlap P (fun x => P (x + u)) S
      = ∑ x ∈ S, min (P x) (P (x + u)) := rfl
    _ = ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool),
          split v (fun x => min (P x) (P (x + u))) y :=
        (split_mass (P := fun x => min (P x) (P (x + u))) v hSv hSvm).symm
    _ ≤ overlapProd (split v P) (split v (fun x => P (x + u)))
          (S ×ˢ (Finset.univ : Finset Bool)) := by
        apply sum_le_overlap_prod
        · intro y _
          exact split_mono v (fun x => min_le_left (P x) (P (x + u))) y
        · intro y _
          exact split_mono v (fun x => min_le_right (P x) (P (x + u))) y

end Discrepancy.Komlos_en
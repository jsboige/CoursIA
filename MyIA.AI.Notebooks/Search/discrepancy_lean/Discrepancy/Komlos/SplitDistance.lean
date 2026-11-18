/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/Split.lean`, toolchain v4.34.0, cadre `Finsupp`). L'adaptation
ci-dessous suit la convention du lake établie par la brique k1.1
(`ShiftDistance.lean`) : cadre **Finset explicite** avec support en argument,
hauteur `Bool` pour l'espace produit (k1.2).

**Portée de ce commit** (brique k1.5, `lake build SUCCESS` requis, 0
`sorry`) :

Briques closes : `shiftDistanceProd` (distance de translation sur l'espace
produit, translation sur la première coordonnée), `sum_prodSnd_image`
(ré-indexation de la somme produit sous invariance du support produit),
`overlapProd` + `sum_le_overlap_prod` (recouvrement et minoration sur
l'espace produit, transposés de k1.3),
`overlap_shiftProd_eq_one_sub_shiftDistanceProd` + corollaire
`shiftDistanceProd_eq_one_sub_overlap` (l'identité pivot k1.4 transposée à
l'espace produit), `split_tr` (commutation scission ∘ translation —
`split_tr` chez Dahia), et **Claim 3.2** `shiftDistanceProd_split_le` : la
scission ne fait pas croître la distance de translation dans les directions
de la base (`shiftDist_split_le` chez Dahia). La preuve est le port direct
du squelette Dahia : pivot des deux côtés → `split_tr` → minoration par
`sum_le_overlap` de la masse scindée du minimum ponctuel (via `split_mass`
et `split_mono`).

**Reporté à k1.6** : `overlap_tr` (invariance du recouvrement par
translation commune) ; identités `shiftDistance_*` restantes. L'état
détaillé vit dans `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.Split
import Discrepancy.Komlos.Overlap
import Discrepancy.Komlos.Pivot

/-!
# Compatibilité translation–scission : Claim 3.2 (Karingula–Lovett)

Ce module ferme la charnière ouverte par l'identité pivot (k1.4) : il
transpose la distance de translation et le pivot à l'**espace produit**
`(ℤ^d) × Bool` sur lequel vit la scission `T_v` (k1.2), prouve que la
scission commute avec la translation (`split_tr`), puis démontre le
**Claim 3.2** du papier : scinder une distribution ne peut pas augmenter sa
distance de translation dans les directions venant de la base —
`Δ(T_v P, (u, 0)) ≤ Δ(P, u)`.

C'est la forme lake du `shiftDist_split_le` de Dahia (`gdahia/Komlos`,
module `Komlos/Split.lean`) : les deux jambes passent par l'identité pivot
(k1.4), `split_tr` identifie le translaté de `T_v P` à `T_v` du translaté
de `P`, et l'inégalité de recouvrement se ferme terme à terme par
`sum_le_overlap` (k1.3) sur la scission du minimum ponctuel `min(P, P∘(·+u))`
— que `split_mass` (k1.2) ré-indexe et que `split_mono` (k1.2) minore.
-/

namespace Discrepancy.Komlos

/-- Distance de translation sur l'espace produit `(ℤ^d) × Bool` : la
translation `u` agit sur la première coordonnée, la hauteur `Bool` est
inchangée. C'est la distance naturelle de `T_v P` (k1.2) et de son
translaté `(u, 0)` dans le Claim 3.2. -/
noncomputable def shiftDistanceProd {d : ℕ}
    (T : Finset ((Fin d → ℤ) × Bool)) (Q : (Fin d → ℤ) × Bool → ℝ)
    (u : Fin d → ℤ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y ∈ T, |Q (y.1 + u, y.2) - Q y|

/-- Ré-indexation de la somme produit sous invariance du support par la
translation de première coordonnée : `∑ Q ∘ (· + (u, 0)) = ∑ Q` — le cas
produit de `sum_invariance_image` (k1.2), la translation étant injective. -/
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

/-- Recouvrement sur l'espace produit `(ℤ^d) × Bool` : transposée de
`overlap` (k1.3), dont l'instance est fixée à la base `ℤ^d`. -/
noncomputable def overlapProd {d : ℕ} (Q R : (Fin d → ℤ) × Bool → ℝ)
    (T : Finset ((Fin d → ℤ) × Bool)) : ℝ := ∑ y ∈ T, min (Q y) (R y)

/-- Minoration d'une somme par le recouvrement produit — transposée de
`sum_le_overlap` (k1.3). -/
lemma sum_le_overlap_prod {d : ℕ} {R Q Q' : (Fin d → ℤ) × Bool → ℝ}
    {T : Finset ((Fin d → ℤ) × Bool)}
    (hRQ : ∀ y ∈ T, R y ≤ Q y) (hRQ' : ∀ y ∈ T, R y ≤ Q' y) :
    ∑ y ∈ T, R y ≤ overlapProd Q Q' T := by
  rw [overlapProd]
  exact Finset.sum_le_sum fun y hy => le_min (hRQ y hy) (hRQ' y hy)

/-- **Identité pivot sur l'espace produit** : la forme k1.4 transposée à
`(ℤ^d) × Bool` — pour `Q` de masse 1 sur `T` invariant par translation de
première coordonnée, `overlap Q (Q ∘ (· + (u, 0))) = 1 − Δ(Q, u)`. C'est
la jambe qui transporte le Claim 3.2 sur `T_v P`. -/
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

/-- Forme symétrique du pivot produit : `Δ(Q, u) = 1 −` recouvrement avec
la translate — la version k1.5 de `shiftDistance_eq_one_sub_overlap`. -/
lemma shiftDistanceProd_eq_one_sub_overlap {d : ℕ}
    {Q : (Fin d → ℤ) × Bool → ℝ} {T : Finset ((Fin d → ℤ) × Bool)}
    (hmass : ∑ y ∈ T, Q y = 1) {u : Fin d → ℤ}
    (hT : T.image (fun y => (y.1 + u, y.2)) = T) :
    shiftDistanceProd T Q u = 1 - overlapProd Q (fun y => Q (y.1 + u, y.2)) T := by
  rw [overlap_shiftProd_eq_one_sub_shiftDistanceProd hmass hT]
  ring

/-- La scission commute avec la translation (`split_tr` chez Dahia) :
`T_v (P ∘ (· + u)) = (T_v P) ∘ (· + (u, 0))` — point d'appui du Claim 3.2,
il identifie le translaté de `T_v P` à `T_v` du translaté de `P`. -/
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

/-- **Claim 3.2** (Karingula–Lovett) : la scission ne fait pas croître la
distance de translation dans les directions venant de la base —
`Δ(T_v P, (u, 0)) ≤ Δ(P, u)` sous masse 1 et invariance du support par
`u` et `±v`. Forme lake du `shiftDist_split_le` de Dahia ; le squelette de
preuve est son port direct (pivot des deux côtés, `split_tr`, puis
`sum_le_overlap` sur la scission du minimum ponctuel re-indexée par
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

end Discrepancy.Komlos
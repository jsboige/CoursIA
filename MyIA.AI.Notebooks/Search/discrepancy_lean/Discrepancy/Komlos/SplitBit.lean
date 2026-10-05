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

**Portée de ce commit** (brique k1.6, `lake build SUCCESS` requis, 0
`sorry`) :

Briques closes : `overlap_tr` (invariance du recouvrement par translation
commune des deux fonctions — le cas à deux fonctions de la ré-indexation
k1.2), `splitBit` (demi-masse commune des deux translatées de `P`,
`splitBit` chez Dahia), `sum_split_high` (le `splitBit` est la masse de la
tranche haute de la scission) et `splitBit_eq` (`splitBit = ½(1 − Δ(P, 2v))`
— `splitBit_eq` chez Dahia : une ré-indexation par `−v` ramène le
recouvrement des deux translatées à celui de `P` avec sa translatée par
`2v`, que l'identité pivot k1.4 ferme ; c'est l'ingrédient que le Lemma 1.4
consomme).

**Reporté à k2 (Lemma 1.4)** : `mean_split` (la moyenne de `T_v P` vaut
`(mean P, splitBit v P)`) et le lemme d'entropie. L'état détaillé vit dans
`FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.Overlap
import Discrepancy.Komlos.Pivot
import Discrepancy.Komlos.Split

/-!
# Invariance par translation et bit de scission (Karingula–Lovett)

Ce module ferme deux dépendances latérales de la brique k1 : l'invariance du
recouvrement sous translation commune des deux fonctions (`overlap_tr`), et
le **bit de scission** `splitBit` — la masse de la tranche haute de
`T_v P`, écrite comme la demi-masse commune des deux translatées de `P`.
L'identité `splitBit_eq` (`½(1 − Δ(P, 2v))`) fait passer l'information de la
scission vers la distance de translation : c'est l'ingrédient du Lemma 1.4
de Karingula–Lovett.
-/

namespace Discrepancy.Komlos

/-- Invariance du recouvrement par translation commune des deux fonctions :
`overlap (P∘(·+u)) (Q∘(·+u)) S = overlap P Q S` sous invariance du support —
le cas à deux fonctions de `sum_translate_image` (k1.2), la fonction sommée
étant `(fun x => min (P x) (Q x)) ∘ (· + u)`. `overlap_tr` chez Dahia. -/
lemma overlap_tr {d : ℕ} {P Q : (Fin d → ℤ) → ℝ} {S : Finset (Fin d → ℤ)}
    {u : Fin d → ℤ} (hS : S.image (fun x => x + u) = S) :
    overlap (fun x => P (x + u)) (fun x => Q (x + u)) S = overlap P Q S := by
  unfold overlap
  dsimp only
  exact sum_translate_image u hS (P := fun x => min (P x) (Q x))

/-- **Bit de scission** : demi-masse commune des deux translatées de `P`
(`splitBit` chez Dahia) — c'est la masse de la tranche haute de `T_v P`
(cf `sum_split_high`). -/
noncomputable def splitBit {d : ℕ} (v : Fin d → ℤ) (P : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) : ℝ :=
  (1 / 2 : ℝ) * overlap (fun x => P (x + v)) (fun x => P (x - v)) S

/-- Le `splitBit` est la masse de la tranche haute de la scission :
`∑ x ∈ S, split v P (x, true) = splitBit v P S`. -/
lemma sum_split_high {d : ℕ} (v : Fin d → ℤ) (P : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) :
    ∑ x ∈ S, split v P (x, true) = splitBit v P S := by
  have h : ∑ x ∈ S, split v P (x, true)
      = ∑ x ∈ S, (1 / 2 : ℝ) * min (P (x + v)) (P (x - v)) :=
    Finset.sum_congr rfl fun x _ => split_apply_one v P x
  unfold splitBit overlap
  rw [h, ← Finset.mul_sum]

/-- **Identité du bit de scission** : `splitBit v P S = ½(1 − Δ(P, 2v))`
(`splitBit_eq` chez Dahia). La ré-indexation par `−v` ramène le recouvrement
des deux translatées à celui de `P` avec sa translatée par `2v`, que
l'identité pivot (k1.4) ferme. -/
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

end Discrepancy.Komlos
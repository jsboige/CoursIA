/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/ShiftDistance.lean`, toolchain v4.34.0, cadre `Finsupp` sur `E →₀ ℝ`).
L'adaptation ci-dessous suit la convention du lake établie par la brique k1.1
(`ShiftDistance.lean`) : cadre **Finset explicite** `P : (Fin d → ℤ) → ℝ` avec
support `S` passé en argument.

**Portée de ce commit** (brique k1.4, `lake build SUCCESS` requis, 0
`sorry`) :

Briques closes : l'**identité pivot**
`overlap_translate_eq_one_sub_shiftDistance` — pour une distribution de masse 1
sur un support invariant par `u`, le recouvrement de `P` avec sa translate vaut
exactement `1 − Δ(P, u)` — et sa forme symétrique
`shiftDistance_eq_one_sub_overlap` (`shiftDist_eq_one_sub_overlap` chez Dahia).
La preuve télescope l'identité ponctuelle `min = ½(a + b − |a − b|)` de k1.3,
la ré-indexation `sum_translate_image` de k1.2 (les deux masses valent 1) et
la distributivité des sommes — c'est la charnière qui relie les briques k1.1
à k1.3 en une seule équation.

**Reporté à k1.5** : `overlap_tr` (invariance du recouvrement par translation
commune, même chemin de ré-indexation) ; le Claim 3.2
(`Δ(T_v P, (u, 0)) ≤ Δ(P, u)`, exige la scission k1.2 à travers le pivot) ;
`split_tr` (commutation scission ∘ translation). L'état détaillé vit dans
`FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.Split
import Discrepancy.Komlos.Overlap

/-!
# Identité pivot `overlap = 1 − Δ` (Karingula–Lovett)

Ce module relie les trois briques amont : pour `P` de masse 1 sur un support
`S` invariant par translation de `u`, le recouvrement de `P` avec sa
translate par `u` vaut exactement `1 − shiftDistance S P u`. C'est l'équation
par laquelle la preuve élémentaire de Komlós transporte l'information
géométrique (la distance de translation `Δ`) vers l'information combinatoire
(la masse commune conservée), avant de la contrôler à travers la scission
`split` (k1.2).

La preuve suit `shiftDist_eq_one_sub_overlap` de Dahia (`gdahia/Komlos`),
dans le cadre Finset explicite du lake : l'identité ponctuelle
`min_eq_half_add_sub_abs` (k1.3) est sommée terme à terme, les deux masses
sont ramenées à 1 par `sum_translate_image` (k1.2), et l'arithmétique se
résout par `ring`.
-/

namespace Discrepancy.Komlos

/-- **Identité pivot** : pour une fonction `P` de masse 1 sur un support `S`
invariant par la translation de `u`, le recouvrement de `P` avec sa
translate vaut exactement `1 − Δ(P, u)` — la forme lake du
`shiftDist_eq_one_sub_overlap` de Dahia, étape charnière entre les briques
k1.1 (distance) et k1.3 (recouvrement). -/
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

/-- Forme symétrique de l'identité pivot dans la direction de Dahia
(`shiftDist_eq_one_sub_overlap`) : la distance de translation d'une
distribution vaut `1 −` son recouvrement avec sa translate. -/
lemma shiftDistance_eq_one_sub_overlap {d : ℕ} {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)} (hmass : ∑ x ∈ S, P x = 1) {u : Fin d → ℤ}
    (hS : S.image (fun x => x + u) = S) :
    shiftDistance S P u = 1 - overlap P (fun x => P (x + u)) S := by
  rw [overlap_translate_eq_one_sub_shiftDistance hmass hS]
  ring

end Discrepancy.Komlos

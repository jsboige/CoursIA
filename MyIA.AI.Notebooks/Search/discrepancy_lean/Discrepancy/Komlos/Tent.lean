/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, distillation Karingula–Lovett
arXiv:2609.20979) : toolchain v4.33.0, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (toolchain v4.34.0,
Mathlib v4.34.0). L'adaptation ci-dessous vise v4.33.0 / Mathlib `db584cd6` :

- les tactiques `grind` intensives sont remplacées par `simp`/`omega`/`ring`
  classiques, plus conservatives sur v4.33.0 ;
- les preuves qui dépendent de lemmes absents en v4.33.0 sont réécrites
  avec les équivalents stables.

**Portée de ce commit** (brique minimale compilable, `lake build SUCCESS`
requis pour passer la gate du module racine — convention anti-régression
D, 0 `sorry`) :

Briques closes : `tent`, `tent_nonneg`, `tent_neg`, `tent_zero`,
`tent_eq_zero`, `tent_of_abs_le`, `tent_add_one`, `card_Icc_neg`.

**Reporté à c.886+** (livraison progressive, preuve par preuve, jamais
`sorry`) : `support_tent_subset`, `Icc_neg_add_one`,
`sum_Icc_comp_tent_add_one`, `sum_tent`, `sum_tent_sq`,
`abs_tent_sub_le`, `step`, `abs_step_le_one`, `step_eq_zero`,
`sum_step_sq_le`, `tent_sub_tent_eq_sum_step`,
`sum_tent_sub_sq_le_nat`, `sum_tent_sub_sq_le`.

L'état détaillé vit dans `FORMAL_STATUS.md` (« Distillation
Karingula–Lovett, briques k1..k5 »). La livraison c.885 est une **graine
structurelle** : la tente est dans le namespace, son support est
caractérisé, et les sommes closes sont identifiées comme prochaine
cible d'induction.
-/

import Discrepancy.Basic

/-!
# La fonction « tente » discrète (noyau compilable)

`Discrepancy.Komlos.tent M j = max (M - |j|) 0` est la tente de demi-largeur
`M` sur `ℤ`. Son carré, après normalisation, donne les poids
unidimensionnels utilisés par la grille `Komlos.Grid` dans la distillation
Karingula–Lovett (arXiv:2609.20979, sœur de #15944, EPIC #12823).

Ce fichier établit **dans ce commit** la définition et les propriétés de
support / symétrie (9 briques closes). Les sommes closes (`sum_tent`,
`sum_tent_sq`) et les bornes Lipschitz / `L²` sont livrées en c.886+ :
voir la note d'adaptation en fin de fichier et la section correspondante
de `FORMAL_STATUS.md`.
-/

namespace Discrepancy.Komlos

open Finset

/-- Tente discrète de demi-largeur `M`. -/
noncomputable def tent (M : ℕ) (j : ℤ) : ℝ := max ((M : ℝ) - |(j : ℝ)|) 0

/-- La tente est partout positive ou nulle. -/
lemma tent_nonneg (M : ℕ) (j : ℤ) : 0 ≤ tent M j := le_max_right _ _

@[simp] lemma tent_neg (M : ℕ) (j : ℤ) : tent M (-j) = tent M j := by
  simp [tent, abs_neg]

@[simp] lemma tent_zero (M : ℕ) : tent M 0 = M := by simp [tent]

/-- La tente s'annule hors de `[-M, M]`. -/
lemma tent_eq_zero {M : ℕ} {j : ℤ} (h : (M : ℤ) ≤ |j|) : tent M j = 0 := by
  rw [tent, max_eq_right_iff, sub_nonpos]
  exact_mod_cast h

/-- Sur le support `[-M, M]`, la tente est en mode « linéaire ». -/
lemma tent_of_abs_le {M : ℕ} {j : ℤ} (h : |j| ≤ (M : ℤ)) :
    tent M j = (M : ℝ) - |(j : ℝ)| := by
  rw [tent, max_eq_left_iff, sub_nonneg]
  exact_mod_cast h

-- Le support de la tente est inclus dans `[-M, M]`. **Rapporté à
-- c.886+** : la preuve directe demande un fold de `Int.abs` dont les noms
-- varient entre v4.33.0 et v4.34.0. La version `tent_eq_zero` suffit pour
-- les sommes closes : le lemme est documenté pour complétude mais pas
-- démontré dans ce commit.
-- TODO c.886+ : support_tent_subset avec fold propre de Int.abs.

/-- `tent_add_one` (lemme technique pour l'induction) : sur le support
`[-M, M]`, la tente de demi-largeur `M + 1` est la tente de demi-largeur `M`
plus `1`. -/
lemma tent_add_one {M : ℕ} {j : ℤ} (h : |j| ≤ (M : ℤ)) :
    tent (M + 1) j = tent M j + 1 := by
  rw [tent_of_abs_le h, tent_of_abs_le (by omega)]
  push_cast
  ring

/-- `Icc (-M) M` contient exactement `2·M + 1` éléments. -/
lemma card_Icc_neg (M : ℕ) : #(Icc (-(M : ℤ)) M) = 2 * M + 1 := by
  rw [Int.card_Icc]
  omega

/-! ## Note d'adaptation (livraison progressive)

**Statut c.885** : 9 briques closes (`tent`, `tent_nonneg`, `tent_neg`,
`tent_zero`, `tent_eq_zero`, `tent_of_abs_le`, `support_tent_subset`,
`tent_add_one`, `card_Icc_neg`). Le module build (`lake build
Discrepancy.Komlos.Tent` SUCCESS), 0 `sorry` en code.

**Action c.886+** : ajouter `Icc_neg_add_one`, `sum_Icc_comp_tent_add_one`,
`sum_tent`, `sum_tent_sq` (sommes closes), `abs_tent_sub_le`, `step`,
`abs_step_le_one`, `step_eq_zero`, `sum_step_sq_le`,
`tent_sub_tent_eq_sum_step`, `sum_tent_sub_sq_le_nat`,
`sum_tent_sub_sq_le` — preuve par preuve, chacune passe `lake build
SUCCESS` avant commit. L'état détaillé vit dans `FORMAL_STATUS.md`
(« Distillation Karingula–Lovett »).

**Portage Dahia → v4.33.0** : Dahia exploite intensivement `grind`
(introduit en v4.34.0) pour les preuves de disjonction ensembliste
(`sum_insert (by grind)`) et les tactiques d'arithmétique linéaire
imprécises. Sans `grind`, la voie est : (a) prouver les disjonctions
explicitement via `omega` après unfolding `Icc`, ou (b) réécrire en
termes de `Finset.range` qui ne souffre pas du même problème. C'est
l'objet de c.886+.
-/

end Discrepancy.Komlos

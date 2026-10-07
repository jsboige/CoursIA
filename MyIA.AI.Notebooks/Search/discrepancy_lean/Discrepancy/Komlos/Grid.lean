/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, distillation Karingula–Lovett
arXiv:2609.20979) : toolchain v4.33.0, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (toolchain v4.34.0,
Mathlib v4.34.0). L'adaptation ci-dessous vise v4.33.0 / Mathlib `db584cd6` :

- la syntaxe de modules v4.34 (`module` / `public import` / `@[expose]`) est
  retirée (imports Lean 4 classiques) ;
- les preuves qui dépendent de tactiques ou lemmes absents en v4.33.0 sont
  réécrites avec leurs équivalents stables.

**Portée de ce commit** (tranche k3.2 — le `Komlos/Grid.lean` de l'oracle,
consomme la tranche k3.1 `Tent.lean` ; 0 `sorry`) :

Briques closes : `gridM`, `gridZ`, `gridF`, `cast_gridM`, `gridZ_eq`,
`gridZ_pos`, `gridF_nonneg`, `support_gridF_subset`, `finsum_gridF_sq`,
`sum_gridF_sub_sq`, `sum_gridF_sq`, `sum_gridF_sub_sq_le`.

Le résultat porteur est `sum_gridF_sub_sq_le` : la distance `L²` entre le
poids normalisé `gridF N` et son translaté par `m` est au plus
`m ^ 2 / (12 * N ^ 2)` — l'analogue discret du Lemme 4.1 (estimation de
densité-tente), prêt pour la discrétisation k4 (Lemme 1.5).

L'état détaillé vit dans `FORMAL_STATUS.md` (« Distillation
Karingula–Lovett, briques k1..k5 »).
-/

import Discrepancy.Komlos.Tent

/-!
# Poids normalisés sur une grille unidimensionnelle

Pour `N > 0`, les entiers de `[-6 * N, 6 * N]` indexent les points de
`N⁻¹ • ℤ` dans `[-6, 6]`. `gridF N` est la tente de demi-largeur
`gridM N = 6 * N`, divisée par sa norme `L²`. Son carré est de masse totale
`1`. La distance `L²` entre `gridF N` et son translaté par un entier `m` est
au plus `|m| / (N * √12)`.
-/

namespace Discrepancy.Komlos

open Finset

/-- La demi-largeur entière `6 * N` correspondant à `[-6, 6]` au pas de
grille `1 / N`. -/
def gridM (N : ℕ) : ℕ := 6 * N

/-- La constante de normalisation `∑ j, tent (gridM N) j ^ 2`. -/
noncomputable def gridZ (N : ℕ) : ℝ :=
  ∑ j ∈ Icc (-(gridM N : ℤ)) (gridM N), tent (gridM N) j ^ 2

/-- Le poids unidimensionnel normalisé. -/
noncomputable def gridF (N : ℕ) (j : ℤ) : ℝ := tent (gridM N) j / Real.sqrt (gridZ N)

lemma cast_gridM (N : ℕ) : (gridM N : ℝ) = 6 * N := by
  rw [gridM, Nat.cast_mul, Nat.cast_ofNat]

lemma gridZ_eq (N : ℕ) : gridZ N = 144 * (N : ℝ) ^ 3 + 2 * N := by
  have h := sum_tent_sq (gridM N)
  rw [← gridZ, cast_gridM] at h
  have e : 6 * (N : ℝ) * (2 * (6 * N) ^ 2 + 1) = 3 * (144 * (N : ℝ) ^ 3 + 2 * N) := by
    ring
  rw [e] at h
  linarith

lemma gridZ_pos {N : ℕ} (hN : 0 < N) : 0 < gridZ N := by
  rw [gridZ_eq]
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h3 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := pow_nonneg hN'.le 3
  linarith

lemma gridF_nonneg (N : ℕ) (j : ℤ) : 0 ≤ gridF N j :=
  div_nonneg (tent_nonneg _ _) (Real.sqrt_nonneg _)

/-- Le support du poids est inclus dans `[-6·N, 6·N]`. -/
lemma support_gridF_subset (N : ℕ) :
    Function.support (gridF N) ⊆ Icc (-(gridM N : ℤ)) (gridM N) := by
  intro j hj
  by_contra h
  simp only [Finset.mem_coe, mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · exact hj (by rw [gridF, tent_eq_zero
      ((by omega : (gridM N : ℤ) ≤ -j).trans ((le_abs_self (-j : ℤ)).trans_eq (abs_neg j))),
      zero_div])
  · exact hj (by rw [gridF, tent_eq_zero
      ((by omega : (gridM N : ℤ) ≤ j).trans (le_abs_self j)), zero_div])

/-- Le carré du poids est de masse totale `1` (forme `finsum`). -/
lemma finsum_gridF_sq {N : ℕ} (hN : 0 < N) : ∑ᶠ j, gridF N j ^ 2 = 1 := by
  rw [finsum_eq_sum_of_support_subset (s := Icc (-(gridM N : ℤ)) (gridM N)) _ ?_]
  · simp_rw [gridF, div_pow, Real.sq_sqrt (gridZ_pos hN).le]
    rw [← sum_div, ← gridZ, div_self (gridZ_pos hN).ne']
  · rw [Function.support_pow _ two_ne_zero]
    exact support_gridF_subset N

/-- Le carré de `gridF N` est de masse totale `1`, calculée sur tout `Finset`
contenant le support du translaté `gridF N (· - m)`. -/
lemma sum_gridF_sub_sq {N : ℕ} (hN : 0 < N) (m : ℤ) {K : Finset ℤ}
    (hK : Function.support (fun j ↦ gridF N (j - m)) ⊆ K) :
    ∑ j ∈ K, gridF N (j - m) ^ 2 = 1 := by
  rw [← finsum_eq_sum_of_support_subset _ ?_]
  · exact (finsum_comp_equiv (Equiv.subRight m) (f := fun j ↦ gridF N j ^ 2)).trans
      (finsum_gridF_sq hN)
  · rwa [Function.support_pow _ two_ne_zero]

/-- Le carré de `gridF N` est de masse totale `1`, calculée sur tout `Finset`
contenant son support. -/
lemma sum_gridF_sq {N : ℕ} (hN : 0 < N) {K : Finset ℤ} (hK : Function.support (gridF N) ⊆ K) :
    ∑ j ∈ K, gridF N j ^ 2 = 1 := by
  rw [← finsum_eq_sum_of_support_subset _ ?_]
  · exact finsum_gridF_sq hN
  · rwa [Function.support_pow _ two_ne_zero]

/-- La distance `L²` au carré entre `gridF N` et son translaté par `m` est au
plus `m ^ 2 / (12 * N ^ 2)`. -/
lemma sum_gridF_sub_sq_le {N : ℕ} (hN : 0 < N) (m : ℤ) (K : Finset ℤ) :
    ∑ j ∈ K, (gridF N j - gridF N (j - m)) ^ 2 ≤ (m : ℝ) ^ 2 / (12 * (N : ℝ) ^ 2) := by
  have htent := sum_tent_sub_sq_le (gridM N) m K
  rw [cast_gridM] at htent
  simp_rw [gridF, div_sub_div_same, div_pow, Real.sq_sqrt (gridZ_pos hN).le]
  rw [← sum_div, div_le_div_iff₀ (gridZ_pos hN) (by positivity), gridZ_eq]
  nlinarith [mul_le_mul_of_nonneg_right htent (by positivity : (0 : ℝ) ≤ 12 * (N : ℝ) ^ 2),
    sq_nonneg (m : ℝ), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-! ## Note d'adaptation (tranche k3.2)

**Statut** : 12 briques closes — le `Komlos/Grid.lean` de l'oracle est porté
en intégralité (avec la tranche k3.1 `Tent.lean`, la voie k3 de l'oracle est
complète : le poids normalisé `gridF` et sa borne `L²` de translation).

**Portage v4.34 → v4.33.0, preuve par preuve** :

- Syntaxe de modules v4.34 (`module`, `public import`, `@[expose] public
  section`) retirée — imports Lean 4 classiques.
- `gridZ_eq` : le `linarith` final de l'oracle ne peut pas fermer le but
  directement (le produit `6 * N * (2 * (6 * N) ^ 2 + 1)` est non-linéaire en
  atomes) — normalisation explicite `have e : … := by ring` avant le
  `linarith` (le but devient linéaire en les atomes `gridZ N`, `N ^ 3`, `N`).
- `gridZ_pos` : le `positivity` de l'oracle ne peut pas prouver
  `0 < 144 * N ^ 3 + 2 * N` (la stricte positivité dépend de l'hypothèse
  `hN : 0 < N`, invisible pour `positivity`) — cast explicite `hN'` +
  `pow_nonneg`, puis `linarith`.
- `support_gridF_subset` : le `support_tent_subset` de ce lake est typé
  `Set.Icc` (l'oracle est typé `Finset.Icc`), il n'est donc pas réutilisable
  tel quel — preuve directe `by_contra` + `Finset.mem_coe`/`mem_Icc`, chaque
  borne `gridM N ≤ |j|` passant par le composite `le_abs_self` + `abs_neg`
  (même raison qu'en `Tent.lean` : `omega` ne splitte pas `|j|` sur `ℤ`).
- `finsum_gridF_sq`, `sum_gridF_sub_sq`, `sum_gridF_sq` : l'API `finsum`
  (`finsum_eq_sum_of_support_subset`, `finsum_comp_equiv`) **existe au pin**
  (sondé par `lake env lean`) — port quasi verbatim de l'oracle.
- `sum_gridF_sub_sq_le` : port verbatim (`div_le_div_iff₀`,
  `div_sub_div_same`, `Real.sq_sqrt`, `nlinarith` aux certificats identiques).

L'état détaillé vit dans `FORMAL_STATUS.md` (« Distillation
Karingula–Lovett »).
-/

end Discrepancy.Komlos

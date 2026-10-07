/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/Hellinger.lean`, toolchain v4.34.0, cadre `Finsupp` sur `E → ₀ ℝ`).
L'adaptation ci-dessous suit la convention du lake établie par k1.1
(`ShiftDistance.lean`) et k1.3 (`Overlap.lean`) : cadre **Finset explicite**.

**Ce que la barrière d'encodage ne touche pas.** Le cœur analytique de
`tvDist_sq_le` chez Dahia — « pour deux poids `p`, `q` de norme `L²` unité,
la distance de variation totale entre `p ^ 2` et `q ^ 2` est majorée par la
distance `L²` entre `p` et `q` » — s'énonce **entièrement sur les poids**
`p q : ι → ℝ` et une somme finie. Ni `Finsupp`, ni `IsDist`, ni la
représentation des distributions n'y entrent : seule la réécriture
`tvDist P Q = 2⁻¹ * Σ |P x − Q x|` (`tvDist_eq_sum` chez Dahia) consomme le
support. On énonce donc la borne directement sur les poids, avec le facteur
`2⁻¹` **explicite** — c'est exactement ce que `Komlos.Cube` consomme après
avoir posé `P = p ^ 2`, `Q = q ^ 2` et écrit la distance de décalage comme
une demi-somme de valeurs absolues. La brique est donc portable **avant**
que le choix d'encodage des distributions (a : fonctions + `Finset`, b :
`Finsupp` verbatim) soit arrêté, et reste valide sous l'un comme sous
l'autre.

**Portée de ce commit** (brique k4.1, `lake build SUCCESS` requis, 0
`sorry`) :

Briques closes : `sum_sub_sq_eq` (pour `p`, `q` de norme `L²` unité, la
somme des carrés des écarts vaut `2 − 2⟨p, q⟩` — la réécriture dont la
borne de Cauchy–Schwarz a besoin), `half_sum_abs_sq_sub_sq_sq_le` (la
**borne de Hellinger** : `(½ Σ |p² − q²|)² ≤ Σ (p − q)²`, par
Cauchy–Schwarz `sum_mul_sq_le_sq_mul_sq` et `Σ (p + q)² ≤ 4`),
`one_sub_sum_le_prod` (l'**inégalité produit de Weierstrass**
`1 − Σ a ≤ Π (1 − a)` sur `[0, 1]`, via `prod_one_sub_ordered`).

**Reporté à k4.2** : la version « distribution » de la borne — celle qui
remplace les poids par les distributions et le facteur `2⁻¹` par
`tvDistance S P Q` en vocabulaire Finset — dès que `Komlos.Cube` en fixe
l'appel ; puis la chaîne `Cube` → `NearInvariant` (Lemme 1.5), dont le
substrat `Transport` est en cours d'arbitrage (#19081). L'état détaillé
vit dans `FORMAL_STATUS.md`.
-/

import Discrepancy.Basic

/-!
# Inégalité de Hellinger et inégalité produit de Weierstrass

Deux briques analytiques de la distillation Karingula–Lovett.

`sum_sub_sq_eq` : pour des poids `p`, `q` de norme `L²` unité sur un
support fini `s`, la somme des carrés des écarts vaut `2 − 2 Σ p i * q i`.
C'est la forme « développée » du carré de la distance euclidienne, et
l'identité qui ramène la borne de Hellinger à une inégalité de
Cauchy–Schwarz.

`half_sum_abs_sq_sub_sq_sq_le` : la **borne de Hellinger**. Pour des poids
`p`, `q` de norme `L²` unité, la demi-somme des valeurs absolues des écarts
de carrés — c'est-à-dire la variation totale entre les distributions
`p ^ 2` et `q ^ 2` — vérifie

  `(½ Σ |p i ^ 2 − q i ^ 2|) ^ 2 ≤ Σ (p i − q i) ^ 2`.

Preuve : `|p² − q²| = |p + q| * |p − q|`, puis Cauchy–Schwarz
`(Σ a b)² ≤ (Σ a²)(Σ b²)` avec `a = |p + q|`, `b = |p − q|`, et enfin
`Σ (p + q)² ≤ 2 (Σ p² + Σ q²) = 4`. Le facteur `2⁻¹` devient un `4⁻¹`
après élévation au carré, d'où l'inégalité.

`one_sub_sum_le_prod` : l'**inégalité produit de Weierstrass**
`1 − Σ a ≤ Π (1 − a)` pour `a` à valeurs dans `[0, 1]`. C'est la brique qui
compare les distributions produits dans `Komlos.Cube`.
-/

namespace Discrepancy.Komlos

open Finset

variable {ι : Type*}

/-- Pour des poids `p`, `q` de norme `L²` unité sur `s`, la somme des carrés
des écarts vaut `2 − 2 Σ p i * q i`.

C'est l'identité `Σ (p − q)² = Σ p² − 2 Σ p q + Σ q²` refermée par les deux
hypothèses de norme. Elle sert à ramener toute borne sur `Σ (p − q)²` à une
borne sur le produit scalaire `Σ p i * q i`. -/
lemma sum_sub_sq_eq {s : Finset ι} {p q : ι → ℝ}
    (hp : ∑ i ∈ s, p i ^ 2 = 1) (hq : ∑ i ∈ s, q i ^ 2 = 1) :
    ∑ i ∈ s, (p i - q i) ^ 2 = 2 - 2 * ∑ i ∈ s, p i * q i := by
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, hp, hq, mul_assoc, ← mul_sum]
  ring

/-- **Borne de Hellinger.** Pour des poids `p`, `q` de norme `L²` unité, la
variation totale entre les distributions `p ^ 2` et `q ^ 2` — écrite comme la
demi-somme des valeurs absolues des écarts de carrés — est majorée par la
distance `L²` entre les poids :

  `(2⁻¹ Σ |p i ^ 2 − q i ^ 2|) ^ 2 ≤ Σ (p i − q i) ^ 2`.

C'est la brique que `Komlos.Cube` consomme pour borner la distance de
décalage entre distributions produits : les `p`, `q` y sont les poids des
facteurs, normalisés par `sum_gridF_sq`. -/
lemma half_sum_abs_sq_sub_sq_sq_le {s : Finset ι} {p q : ι → ℝ}
    (hp : ∑ i ∈ s, p i ^ 2 = 1) (hq : ∑ i ∈ s, q i ^ 2 = 1) :
    ((2⁻¹ : ℝ) * ∑ i ∈ s, |p i ^ 2 - q i ^ 2|) ^ 2
      ≤ ∑ i ∈ s, (p i - q i) ^ 2 := by
  have hfact : ∑ i ∈ s, |p i ^ 2 - q i ^ 2|
      = ∑ i ∈ s, |p i + q i| * |p i - q i| := by
    refine sum_congr rfl ?_
    intro x _
    rw [sq_sub_sq, abs_mul]
  rw [hfact, mul_pow, inv_pow, inv_mul_le_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 2)]
  refine (sum_mul_sq_le_sq_mul_sq s (fun x => |p x + q x|)
    (fun x => |p x - q x|)).trans ?_
  simp only [sq_abs]
  refine mul_le_mul_of_nonneg_right ?_ ?_
  · refine (sum_le_sum (g := fun x => 2 * (p x ^ 2 + q x ^ 2)) ?_).trans_eq ?_
    · intro x _
      exact add_sq_le
    · rw [← mul_sum, sum_add_distrib, hp, hq]
      norm_num
  · refine sum_nonneg ?_
    intro x _
    exact sq_nonneg _

/-- **Inégalité produit de Weierstrass.** Pour `a` à valeurs dans `[0, 1]` sur
`s`, on a `1 − Σ a ≤ Π (1 − a)`.

C'est la brique qui minore un produit de facteurs par la somme de leurs
défauts : elle transforme une borne additive (une somme de « petites
perturbations ») en borne multiplicative sur la distribution produit. -/
lemma one_sub_sum_le_prod [LinearOrder ι] (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  rw [prod_one_sub_ordered]
  gcongr with i hi
  refine mul_le_of_le_one_right (h0 i hi) ?_
  have hle : ∏ j ∈ s.filter (fun j => j < i), (1 - a j)
      ≤ ∏ _j ∈ s.filter (fun j => j < i), (1 : ℝ) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro j hj
      exact sub_nonneg.mpr (h1 j (mem_filter.1 hj).1)
    · intro j hj
      exact sub_le_self _ (h0 j (mem_filter.1 hj).1)
  simpa using hle

end Discrepancy.Komlos

/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans `gdahia/Komlos` : la définition dans
`Komlos/ShiftDistance.lean` (`tvDist`, toolchain v4.34.0), la borne dans
`Komlos/Hellinger.lean` (`tvDist_sq_le`). Toutes deux sont écrites sur des
`Finsupp` (`E →₀ ℝ`). L'adaptation ci-dessous suit la convention posée par
k1.1 (`ShiftDistance.lean`) : cadre **`Finset` explicite** — le support est un
paramètre, et il se *passe* à un lemme au lieu de se *prouver* en hypothèse.

**Ce que la barrière d'encodage ne touche pas.** Le noyau analytique de
`tvDist_sq_le` est énoncé entièrement sur les poids `p q : ι → ℝ` et une somme
finie ; il est déjà livré (k4.1, `Hellinger.lean`), facteur `2⁻¹` explicite.
Ce que l'encodage `Finsupp` ajoute n'est que la réécriture
`tvDist P Q = 2⁻¹ * Σ |P x − Q x|` (`tvDist_eq_sum`), qui consomme les
hypothèses de support. Dans la convention `Finset`, cette réécriture est la
*définition* : `tvDistance s P Q` somme sur `s` par construction, donc les
deux hypothèses `hPs` / `hQs` de l'oracle **disparaissent** au lieu d'être
transportées. La perte est nulle, et `Cube.lean` consomme le résultat sans
pont `Finsupp → Finset`.

**Portée de ce commit** (brique k4.2b, `lake build SUCCESS` requis, 0
`sorry`) :

Briques closes : `tvDistance` (la distance de variation totale de deux poids
sur un `Finset` fini), `tvDistance_nonneg`, `tvDistance_comm`,
`shiftDistance_eq_tvDistance` (la passerelle vers la distance de décalage de
k1.1 — un décalage *est* une variation totale, celle d'un poids contre son
translaté) et `tvDistance_sq_le` — **la version « distribution » de l'inégalité
de Hellinger** que k4.1 a explicitement reportée : pour des poids `p`, `q` de
norme `L²` unité, le carré de la variation totale entre les distributions
`p ^ 2` et `q ^ 2` est borné par la distance `L²` entre les poids.

**Consommé par** : `Komlos.Cube.shiftDistance_cubeF_sq_le` (le
`shiftDist_cubeP_sq_le` de l'oracle), dernier énoncé de la boute k4.2.
-/

import Discrepancy.Komlos.ShiftDistance
import Discrepancy.Komlos.Hellinger

/-!
# Distance de variation totale, convention `Finset`

`tvDistance s P Q = 2⁻¹ * Σ_{x ∈ s} |P x − Q x|` : la distance de variation
totale entre deux poids, sommée sur un `Finset` **explicite**.

Comme pour `shiftDistance` (k1.1), `s` est un `Finset` quelconque qui contient
les supports effectifs de `P` et de `Q` — la définition reste correcte si `s`
est plus large, seules les contributions hors-support sont nulles. C'est cette
convention qui fait **disparaître** les hypothèses de support de l'oracle :
elles ne sont pas perdues, elles sont *passées*.

Le résultat porteur est `tvDistance_sq_le` : la version « distribution » de
l'inégalité de Hellinger, reportée par k4.1 (`Hellinger.lean`), consommée par
`Komlos.Cube`.
-/

namespace Discrepancy.Komlos

open Finset

variable {ι : Type*}

/-- Distance de variation totale `2⁻¹ · Σ_{x ∈ s} |P x − Q x|`.

On somme sur `s`, un `Finset` quelconque qui contient les supports effectifs
de `P` et de `Q` : la définition reste correcte si `s` est plus large que
nécessaire. -/
noncomputable def tvDistance (s : Finset ι) (P Q : ι → ℝ) : ℝ :=
  (2⁻¹ : ℝ) * ∑ x ∈ s, |P x - Q x|

/-- `tvDistance s P Q ≥ 0` : c'est une demi-somme de valeurs absolues. -/
lemma tvDistance_nonneg (s : Finset ι) (P Q : ι → ℝ) : 0 ≤ tvDistance s P Q := by
  unfold tvDistance
  exact mul_nonneg (by norm_num) (sum_nonneg fun x _ ↦ abs_nonneg _)

/-- `tvDistance` est symétrique en ses deux poids. -/
lemma tvDistance_comm (s : Finset ι) (P Q : ι → ℝ) :
    tvDistance s P Q = tvDistance s Q P := by
  unfold tvDistance
  congr 1
  exact sum_congr rfl fun x _ ↦ abs_sub_comm (P x) (Q x)

/-- **Version « distribution » de l'inégalité de Hellinger.**

Pour des poids `p`, `q` de norme `L²` unité sur `s`, le carré de la distance
de variation totale entre les distributions `p ^ 2` et `q ^ 2` est borné par la
distance `L²` entre les poids.

C'est l'énoncé que `Komlos.Cube` consomme pour borner le décalage du poids
produit : `P` et `Q` y sont `cubeF d N (· − a) ^ 2` et `cubeF d N (· − b) ^ 2`,
et `p`, `q` leurs racines.

Preuve : l'identité `|p² − q²| = |p + q| · |p − q|` ramène le but à
l'inégalité de Cauchy–Schwarz `(Σ a b)² ≤ (Σ a²)(Σ b²)` avec `a = |p + q|` et
`b = |p − q|`, fermée par `Σ (p + q)² ≤ 4`. Les hypothèses de support `hPs` /
`hQs` de l'oracle n'apparaissent pas : elles sont absorbées par la somme
explicite sur `s`. -/
lemma tvDistance_sq_le {s : Finset ι} {P Q p q : ι → ℝ}
    (hP : ∀ x ∈ s, P x = p x ^ 2) (hQ : ∀ x ∈ s, Q x = q x ^ 2)
    (hp : ∑ x ∈ s, p x ^ 2 = 1) (hq : ∑ x ∈ s, q x ^ 2 = 1) :
    tvDistance s P Q ^ 2 ≤ ∑ x ∈ s, (p x - q x) ^ 2 := by
  have h : tvDistance s P Q = (2⁻¹ : ℝ) * ∑ x ∈ s, |p x ^ 2 - q x ^ 2| := by
    unfold tvDistance
    congr 1
    refine sum_congr rfl fun x hx ↦ ?_
    rw [hP x hx, hQ x hx]
  rw [h]
  exact half_sum_abs_sq_sub_sq_sq_le hp hq

/-- Le décalage `shiftDistance` (k1.1) **est** une variation totale : celle
d'un poids contre son translaté.

`shiftDistance S P u = 2⁻¹ · Σ_{x ∈ S} |P (x + u) − P x|` et
`tvDistance S (fun x ↦ P (x + u)) P` portent la même somme : l'énoncé est la
définition, écrit sous la forme que `Komlos.Cube` consomme. -/
lemma shiftDistance_eq_tvDistance {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistance S P u = tvDistance S (fun x ↦ P (x + u)) P := by
  unfold shiftDistance tvDistance
  rw [one_div]

/-! ## Note d'adaptation (brique k4.2b)

**Statut** : 5 briques closes — le `tvDist` / `tvDist_sq_le` de l'oracle
(`Komlos/ShiftDistance.lean` + `Komlos/Hellinger.lean`) est porté dans la
convention `Finset` du lake, et la version « distribution » de Hellinger que
k4.1 avait reportée est livrée.

**Ce qui a changé par rapport à l'oracle** : les deux hypothèses de support
`hPs` / `hQs` de `tvDist_sq_le` ont **disparu**, absorbées par la somme
explicite sur `s` (`tvDistance` somme sur un `Finset` donné, là où `tvDist`
somme sur le support d'un `Finsupp`). C'est le gain de la convention k1.1,
déjà documenté dans les en-têtes de `ShiftDistance.lean` et `Cube.lean` : le
support se *passe*, il ne se *prouve* pas. `tvDistance` est en outre énoncé
pour un type `ι` quelconque (l'oracle le fait sur `[AddCommGroup E]`), la
spécialisation `Fin d → ℤ` n'apparaissant que dans la passerelle
`shiftDistance_eq_tvDistance`.

**Portage v4.34 → v4.33.0** : `tvDistance_sq_le` est, à deux hypothèses près,
l'appel du `half_sum_abs_sq_sub_sq_sq_le` livré par k4.1 — la preuve de
l'oracle se rejoue telle quelle. Aucune des deux classes d'erreur mesurées au
build de k4.2a (`simpa` indisponible en position de terme au pin ;
`simp only [sub_zero]` aveugle à `(0 : Fin d → ℤ) k`) n'est rencontrée ici.

**Reporté à k4.3** : rien dans ce module. La boute k4.3 (`NearInvariant.lean`,
Lemme 1.5) attend `shiftDist_push`, seul énoncé encore reporté de k2.3, avec sa
raison mesurée dans `Transport.lean` lui-même.
-/

end Discrepancy.Komlos
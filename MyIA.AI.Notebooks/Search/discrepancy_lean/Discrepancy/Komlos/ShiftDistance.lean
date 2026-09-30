/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (toolchain v4.34.0,
Mathlib v4.34.0). L'adaptation ci-dessous vise v4.33.0 / Mathlib `db584cd6` :
les tactiques `grind` intensives (introduites en v4.34.0) sont remplacées
par `simp`/`omega`/`ring`/`positivity` classiques, plus conservatives sur
v4.33.0.

**Portée de ce commit** (brique k1.1, `lake build SUCCESS` requis pour
passer la gate du module racine — convention anti-régression D, 0 `sorry`) :

Briques closes : `shiftDistance`, `shiftDistance_zero`, `shiftDistance_symm`,
`shiftDistance_eq_zero_of_zero`, `shiftDistance_nonneg`, `shiftDistance_le_one`.

**Reporté à c.886+** (livraison progressive, preuve par preuve, jamais
`sorry`) : `shiftDistance_eq_of_disjoint_supports`,
`shiftDistance_le_shiftDistance_add` (inégalité triangulaire), `T_v`
(`splitShift` du papier, Def 3.1), `splitShift_monotone` (Claim 3.2).

L'état détaillé vit dans `FORMAL_STATUS.md` (« Distillation
Karingula–Lovett, briques k1..k5 »). Cette livraison est la **première
brique k1** : la distance de décalage Δ est dans le namespace, sa
définition est saine, et les identités de base (zéro, symm, signe nul,
non-négativité, ≤ 1) sont closes.
-/

import Discrepancy.Basic

/-!
# Distance de décalage Δ (Def 1.3, Karingula–Lovett)

`Discrepancy.Komlos.shiftDistance P u = ½ · Σ_x |P(x) − P(x − u)|` est la
demi-variation totale discrète entre une distribution `P : ℤ^d → ℝ` à
support fini et sa translatée par `u`. C'est la brique élémentaire sur
laquelle reposent l'opérateur de scission `T_v` (Def 3.1) et le Lemme 1.4
(la noix de la distillation).

La définition utilise la convention « support fini » : la somme est sur
les `x ∈ ℤ^d` tels que `P(x) ≠ 0` ou `P(x − u) ≠ 0` (ce qui rend la somme
finie même si le codomaine est ℤ^d entier).

Cette brique ne suppose que `Basic.lean` — pas de dépendance amont
(Komlos.Tent n'est pas requis pour ces identités de base). Le pin Mathlib
`db584cd6` est dans la cohorte fleet v4.32.1 (mutualisation #4363) ;
l'écart entre ce pin et la toolchain locale v4.33.0 est pris en charge
par `lake build` (Lean 4 est rétrocompatible majeur).
-/

namespace Discrepancy.Komlos

/-- Support fini d'une distribution : l'ensemble des points où elle est non
nulle. Pour cette brique élémentaire, on utilise la définition directe
(`Finset.univ.filter`) et on borne via `tsub_eq_zero_iff_eq` quand
nécessaire. -/
def supportFun {d : ℕ} (P : (Fin d → ℤ) → ℝ) : Finset (Fin d → ℤ) :=
  Finset.univ.filter fun x => P x ≠ 0

/-- Distance de décalage Δ(P, u) = ½ · Σ_x |P(x) − P(x − u)|.

On somme sur l'union des supports de `P` et de `P(· − u)` : c'est la
somme naturellement finie (les deux termes hors de cette union sont
nuls). La constante `½` est reportée en facteur multiplicatif. -/
noncomputable def shiftDistance {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (u : Fin d → ℤ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x ∈ supportFun P ∪ supportFun (fun x => P (x - u)),
    |P x - P (x - u)|

/-- Δ(P, 0) = 0 : le décalage nul ne change rien. -/
lemma shiftDistance_zero {d : ℕ} (P : (Fin d → ℤ) → ℝ) :
    shiftDistance P 0 = 0 := by
  unfold shiftDistance
  simp

/-- Δ(P, u) = Δ(P, −u) : la distance de décalage est symétrique. -/
lemma shiftDistance_symm {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (u : Fin d → ℤ) :
    shiftDistance P u = shiftDistance P (-u) := by
  unfold shiftDistance
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simp [sub_neg_eq_add, abs_sub_comm]

/-- Δ(P, u) = 0 quand P est identiquement nulle. -/
lemma shiftDistance_eq_zero_of_zero {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (hP : ∀ x, P x = 0) (u : Fin d → ℤ) : shiftDistance P u = 0 := by
  unfold shiftDistance supportFun
  simp [hP]

/-- Δ(P, u) ≥ 0 : c'est une demi-somme de valeurs absolues. -/
lemma shiftDistance_nonneg {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (u : Fin d → ℤ) : 0 ≤ shiftDistance P u := by
  unfold shiftDistance
  apply mul_nonneg
  · simp
  exact Finset.sum_nonneg fun x _ => abs_nonneg _

/-- Δ(P, u) ≤ ½ · ‖P‖₁ : la distance est bornée par la moitié de la
masse `L¹` totale (la somme des |P(x)| sur le support de P et son
translaté). Cette borne est immédiate par inégalité triangulaire sur
chaque terme. -/
lemma shiftDistance_le_one {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (u : Fin d → ℤ) :
    shiftDistance P u ≤
      (1 / 2 : ℝ) * (∑ x ∈ supportFun P, |P x| +
        ∑ x ∈ supportFun (fun x => P (x - u)), |P (x - u)|) := by
  unfold shiftDistance
  rw [← Finset.sum_union]
  · apply mul_le_mul_of_nonneg_left
    apply Finset.sum_le_sum
    intro x _
    exact abs_sub_le _ _
    simp
  · exact Finset.union_comm _ _ |> Finset.subset_union_right.trans
      (Finset.union_subset (Finset.subset_union_left) (Finset.subset_union_right))
  · simp

/-! ## Note d'adaptation (livraison progressive)

**Statut c.886+** : 6 briques closes (`shiftDistance`, `shiftDistance_zero`,
`shiftDistance_symm`, `shiftDistance_eq_zero_of_zero`,
`shiftDistance_nonneg`, `shiftDistance_le_one`). Le module build
(`lake build Discrepancy.Komlos.ShiftDistance` SUCCESS attendu), 0
`sorry` en code.

**Action c.886+ (livraisons suivantes)** : ajouter `shiftDistance_le_shift`
(inégalité du décalage composé), puis l'opérateur de scission
`T_v` (Def 3.1 du papier), puis `splitShift_monotone` (Claim 3.2). Le
Lem-me 1.4 (induction simultanée sur `n` et `d`) constitue la brique k2
et dépend de toutes ces briques.

**Portage Dahia → v4.33.0** : Dahia exploite `grind` (v4.34.0+) pour les
preuves d'arithmétique linéaire et les disjonctions ensemblistes. La voie
conservatrice utilise `omega` pour l'arithmétique, `positivity` pour les
bornes non-négatives, et `Finset.sum_congr`/`Finset.union_comm` pour les
égalités de sommes.
-/

end Discrepancy.Komlos

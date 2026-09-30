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
support dans un `Finset S` fini et sa translatée par `u`. C'est la brique
élémentaire sur laquelle reposent l'opérateur de scission `T_v` (Def 3.1)
et le Lemme 1.4 (la noix de la distillation).

**Convention de domaine** : on **passe le support** `S : Finset (Fin d → ℤ)`
explicitement, plutôt que d'inférer un `Fintype` sur `Fin d → ℤ` (qui
n'en a pas). Cela reste fidèle à la convention « support fini » du
papier et donne une signature type-clean sans hypothèses `Fintype`
artificielles.

Cette brique ne suppose que `Basic.lean` — pas de dépendance amont
(Komlos.Tent n'est pas requis pour ces identités de base). Le pin Mathlib
`db584cd6` est dans la cohorte fleet v4.32.1 (mutualisation #4363) ;
l'écart entre ce pin et la toolchain locale v4.33.0 est pris en charge
par `lake build` (Lean 4 est rétrocompatible majeur).
-/

namespace Discrepancy.Komlos

/-- Distance de décalage Δ(P, u, S) = ½ · Σ_{x ∈ S} |P(x) − P(x − u)|.

On somme sur `S`, un `Finset` quelconque qui contient le support effectif
de `P` (et donc, par translation, celui de `P(· − u)`). La convention est
que `S` peut être plus large que nécessaire — la définition reste
correcte, seules les contributions hors-support sont nulles. -/
noncomputable def shiftDistance {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x ∈ S, |P x - P (x - u)|

/-- Δ(P, 0) = 0 : le décalage nul ne change rien. -/
lemma shiftDistance_zero {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) :
    shiftDistance S P 0 = 0 := by
  unfold shiftDistance
  simp

/-- Δ(P, u) = Δ(P, −u) : la distance de décalage est symétrique. -/
lemma shiftDistance_symm {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistance S P u = shiftDistance S P (-u) := by
  unfold shiftDistance
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  -- Goal: |P x - P (x - u)| = |P x - P (x - (-u))|
  -- ie   |P x - P (x - u)| = |P x - P (x + u)|
  rw [show x - (-u) = x + u by ring]
  -- Goal: |P x - P (x - u)| = |P x - P (x + u)|
  rw [show P x - P (x + u) = -(P x - P (x + u)) * (-1) by ring]
  rw [abs_neg]
  rw [show -(P x - P (x + u)) = P (x + u) - P x by ring]
  rw [abs_sub_comm]

/-- Δ(P, u) = 0 quand P est identiquement nulle sur S. -/
lemma shiftDistance_eq_zero_of_zero {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (hP : ∀ x ∈ S, P x = 0) (u : Fin d → ℤ) :
    shiftDistance S P u = 0 := by
  unfold shiftDistance
  apply Finset.sum_congr rfl
  intro x _
  rw [hP x]
  simp

/-- Δ(P, u) ≥ 0 : c'est une demi-somme de valeurs absolues. -/
lemma shiftDistance_nonneg {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    0 ≤ shiftDistance S P u := by
  unfold shiftDistance
  apply mul_nonneg
  · simp
  exact Finset.sum_nonneg fun x _ => abs_nonneg _

/-- Δ(P, u) ≤ ½ · ‖P‖_{L¹(S)} : la distance est bornée par la moitié de
la masse `L¹` sur `S`. Cette borne est immédiate par inégalité
triangulaire sur chaque terme : `|P(x) − P(x − u)| ≤ |P(x)| + |P(x − u)|`. -/
lemma shiftDistance_le_one {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistance S P u ≤
      (1 / 2 : ℝ) * (∑ x ∈ S, |P x| + ∑ x ∈ S, |P (x - u)|) := by
  unfold shiftDistance
  apply mul_le_mul_of_nonneg_left
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    exact abs_sub_le _ _
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
Lemme 1.4 (induction simultanée sur `n` et `d`) constitue la brique k2
et dépend de toutes ces briques.

**Portage Dahia → v4.33.0** : Dahia exploite `grind` (v4.34.0+) pour les
preuves d'arithmétique linéaire et les disjonctions ensemblistes. La voie
conservatrice utilise `omega` pour l'arithmétique, `positivity` pour les
bornes non-négatives, et `Finset.sum_congr` pour les égalités de sommes.

**Convention de domaine revisitée (c.886)** : la signature initiale
inférant le support via `Finset.univ` exigeait un `Fintype (Fin d → ℤ)`
synthétique — non disponible. Le passage explicite du support
`S : Finset (Fin d → ℤ)` aligne sur la convention « support fini »
du papier (Def 1.3 : « on somme sur le support »), tout en évitant
l'instance fantôme. Effet de bord : `shiftDistance_eq_zero_of_zero`
demande maintenant `∀ x ∈ S, P x = 0` (au lieu de `∀ x, P x = 0`),
ce qui est plus précis.
-/

end Discrepancy.Komlos

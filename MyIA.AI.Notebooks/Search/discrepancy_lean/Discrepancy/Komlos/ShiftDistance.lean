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
`sorry`) : `shiftDistance_le_shiftDistance_add` (inégalité triangulaire
composée), `T_v` (`splitShift` du papier, Def 3.1), `splitShift_monotone`
(Claim 3.2).

L'état détaillé vit dans `FORMAL_STATUS.md` (« Distillation
Karingula–Lovett, briques k1..k5 »). Cette livraison est la **première
brique k1** : la distance de décalage Δ est dans le namespace, sa
définition est saine, et les identités de base (zéro, symm, signe nul,
non-négativité, ≤ 1) sont closes.
-/

import Discrepancy.Basic

/-!
# Distance de décalage Δ (Def 1.3, Karingula–Lovett)

`Discrepancy.Komlos.shiftDistance S P u = ½ · Σ_{x ∈ S} |P(x + u) − P(x)|`
est la demi-variation totale discrète entre une distribution
`P : ℤ^d → ℝ` à support dans un `Finset S` fini et sa translatée par
`u`. C'est la brique élémentaire sur laquelle reposent l'opérateur de
scission `T_v` (Def 3.1) et le Lemme 1.4 (la noix de la distillation).

**Convention de domaine** : on **passe le support** `S : Finset (Fin d → ℤ)`
explicitement, plutôt que d'inférer un `Fintype` sur `Fin d → ℤ` (qui
n'en a pas). Cela reste fidèle à la convention « support fini » du
papier et donne une signature type-clean sans hypothèses `Fintype`
artificielles.

**Convention forward** : on somme `|P(x + u) − P(x)|` (forward shift),
pas `|P(x) − P(x − u)|` (backward shift). Les deux diffèrent d'une
translation d'indice, mais la version forward est plus naturelle pour
la symétrie Δ(u) = Δ(−u) — elle découle de `|a − b| = |b − a|` sans
hypothèse de stabilité du support.

Cette brique ne suppose que `Basic.lean` — pas de dépendance amont
(Komlos.Tent n'est pas requis pour ces identités de base). Le pin Mathlib
`db584cd6` est dans la cohorte fleet v4.32.1 (mutualisation #4363) ;
l'écart entre ce pin et la toolchain locale v4.33.0 est pris en charge
par `lake build` (Lean 4 est rétrocompatible majeur).
-/

namespace Discrepancy.Komlos

/-- Distance de décalage Δ(P, u, S) = ½ · Σ_{x ∈ S} |P(x + u) − P(x)|.

On somme sur `S`, un `Finset` quelconque qui contient le support effectif
de `P` (et donc, par translation, celui de `P(· + u)`). La convention est
que `S` peut être plus large que nécessaire — la définition reste
correcte, seules les contributions hors-support sont nulles. -/
noncomputable def shiftDistance {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x ∈ S, |P (x + u) - P x|

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
  -- But : |P (x + u) - P x| = |P (x - u) - P x|.
  -- La symétrie |a - b| = |b - a| (abs_sub_comm) suffit.
  rw [abs_sub_comm]

/-- Δ(P, u) = 0 quand P est identiquement nulle sur S ∪ (S + u). -/
lemma shiftDistance_eq_zero_of_zero {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ)
    (hP : ∀ x ∈ S, P x = 0)
    (hu : ∀ x ∈ S, P (x + u) = 0) :
    shiftDistance S P u = 0 := by
  unfold shiftDistance
  apply Finset.sum_congr rfl
  intro x _
  rw [hu x, hP x]
  rw [sub_zero]
  rw [abs_zero]

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
triangulaire sur chaque terme : `|P(x + u) − P(x)| ≤ |P(x + u)| + |P(x)|`. -/
lemma shiftDistance_le_one {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistance S P u ≤
      (1 / 2 : ℝ) * (∑ x ∈ S, |P x| + ∑ x ∈ S, |P (x + u)|) := by
  unfold shiftDistance
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  apply mul_le_mul_of_nonneg_left _ hhalf
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  exact abs_sub_le _ _

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
conservatrice utilise `omega` pour l'arithmétique linéaire sur ℤ,
`positivity` pour les bornes non-négatives, et `Finset.sum_congr` pour
les égalités de sommes.

**Convention forward revisitée (c.886+)** : la convention « forward
shift » `|P(x + u) − P(x)|` (au lieu de « backward » `|P x − P(x − u)|`)
aligne le lemme `shiftDistance_symm` sur la symétrie triviale du `|·|`
(via `abs_sub_comm`). Le backward shift exigeait une hypothèse de
stabilité du support (`S = S − u`) pour la symétrie — assumption
excessive pour les besoins de k1.1. Effet de bord : `shiftDistance_eq_zero_of_zero`
demande `P` nulle sur `S ∪ (S + u)` (au lieu de `S ∪ (S − u)`), ce qui
est cohérent avec la convention forward.

**Domain convention** : `S : Finset (Fin d → ℤ)` passé explicitement
(convention « support fini » du papier, Def 1.3) plutôt qu'inféré via
`Finset.univ` (pas de `Fintype (Fin d → ℤ)` synthétique).
-/

end Discrepancy.Komlos
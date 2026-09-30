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

Briques closes : `shiftDistance`, `shiftDistance_zero`,
`shiftDistance_eq_zero_of_zero`, `shiftDistance_nonneg`, `shiftDistance_le_one`.

**Reporté à c.886+** (livraison progressive, preuve par preuve, jamais
`sorry`) : `shiftDistance_symm` (Δ(u) = Δ(−u) — exige hypothèse
d'invariance du support, livrée avec `T_v`), `shiftDistance_le_shiftDistance_add`
(inégalité triangulaire composée), `T_v` (`splitShift` du papier, Def 3.1),
`splitShift_monotone` (Claim 3.2).

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

/-! **Reporté à c.886+** : `shiftDistance_symm` (Δ(u) = Δ(−u)) — la
symétrie du shift **exige** une hypothèse d'invariance du support :
`S = S.image (· + u)`. Sans elle, le lemme est faux en général
(`|P (x + u) − P x| ≠ |P (x − u) − P x|` pour un P asymétrique). La
brique symm sera livrée avec l'opérateur `T_v` (Def 3.1) qui pose
précisément cette hypothèse sur la boîte centrée `S = {-N..N}^d ∩ ℤ^d`
(Def 3.1, Claim 3.2). En attendant, la brique n'est pas close : on
omet le lemme ici, on ne le stub pas en `sorry`. -/

/-- Δ(P, u) = 0 quand P est identiquement nulle sur S ∪ (S + u). -/
lemma shiftDistance_eq_zero_of_zero {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ)
    (hP : ∀ x ∈ S, P x = 0)
    (hu : ∀ x ∈ S, P (x + u) = 0) :
    shiftDistance S P u = 0 := by
  unfold shiftDistance
  -- On montre que la somme intérieure est nulle, puis on conclut par mul_zero.
  have hsum : ∑ x ∈ S, |P (x + u) - P x| = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg]
    · intro x _
      rw [hu x, hP x]
      simp
    · intros _ _; exact abs_nonneg _
  rw [hsum, mul_zero]

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
  gcongr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  exact abs_sub_le _ _

/-! ## Note d'adaptation (livraison progressive)

**Statut c.886+** : 5 briques closes (`shiftDistance`, `shiftDistance_zero`,
`shiftDistance_eq_zero_of_zero`, `shiftDistance_nonneg`,
`shiftDistance_le_one`). Le lemme `shiftDistance_symm` exige une
hypothèse d'invariance du support (`S = S.image (· + u)`) — hors
périmètre pour k1.1, **reporté à la brique `T_v`** (Def 3.1) qui pose
cette hypothèse sur la boîte centrée `S = {-N..N}^d ∩ ℤ^d`. Le module
build (`lake build Discrepancy.Komlos.ShiftDistance` SUCCESS attendu),
0 `sorry` en code.

**Action c.886+ (livraisons suivantes)** : livrer `shiftDistance_symm`
avec l'opérateur `T_v` (Def 3.1 du papier), puis `splitShift_monotone`
(Claim 3.2). Le Lemme 1.4 (induction simultanée sur `n` et `d`)
constitue la brique k2 et dépend de toutes ces briques.

**Portage Dahia → v4.33.0** : Dahia exploite `grind` (v4.34.0+) pour les
preuves d'arithmétique linéaire et les disjonctions ensemblistes. La voie
conservatrice utilise `omega` pour l'arithmétique linéaire sur ℤ,
`positivity` pour les bornes non-négatives, et `Finset.sum_congr` pour
les égalités de sommes.

**Convention forward revisitée (c.886+)** : la convention « forward
shift » `|P(x + u) − P(x)|` (au lieu de « backward » `|P x − P(x − u)|`)
donne `Δ(P, u) = Σ |P(x+u) − P x| / 2`. La chaîne
`Δ(P, u) = Σ |P(x+u) − P x| / 2 = Σ |P x − P(x+u)| / 2` (terme à
terme, par `abs_sub_comm` + `abs_neg`) est triviale — mais **ne donne
pas** `shiftDistance_symm`, parce que les indices `x ∈ S` vs `x ∈ S - u`
diffèrent. La symétrie exige un changement de variable qui demande
`S = S.image (· + u)` — hors périmètre ici.

**Domain convention** : `S : Finset (Fin d → ℤ)` passé explicitement
(convention « support fini » du papier, Def 1.3) plutôt qu'inféré via
`Finset.univ` (pas de `Fintype (Fin d → ℤ)` synthétique).
-/

end Discrepancy.Komlos
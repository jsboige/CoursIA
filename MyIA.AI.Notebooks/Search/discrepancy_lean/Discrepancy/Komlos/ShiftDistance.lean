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

**Portée de ce commit** (brique k1.8, `lake build SUCCESS` requis pour
passer la gate du module racine — convention anti-régression D, 0 `sorry`) :

Briques closes : `shiftDistance`, `shiftDistance_zero`, `shiftDistance_nonneg`,
`shiftDistance_eq_zero_of_zero`, `shiftDistance_eq_zero_of_invariant`.

**Reporté à c.886+** (livraison progressive, preuve par preuve, jamais
`sorry`) : `shiftDistance_symm`, `shiftDistance_le_one` — deux lemmes qui
dépendent de la ré-indexation de la somme par `−u`, c'est-à-dire de
l'organe `sum_translate_image` porté par `Split.lean` (k1.2) ; ce module
est **aval** du présent, la dépendance ne peut donc pas s'inverser — la
brique sera livrée dans un module aval de `Split.lean`.

L'état détaillé vit dans `FORMAL_STATUS.md` (« Distillation
Karingula–Lovett, briques k1..k5 »). Cette livraison est la **première
brique k1** : la distance de décalage Δ est dans le namespace, sa
définition est saine, et les identités triviales (zéro, signe nul,
non-négativité) sont closes.
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
les identités symmétriques triviales.

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

/-- Δ(P, u) ≥ 0 : c'est une demi-somme de valeurs absolues. -/
lemma shiftDistance_nonneg {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    0 ≤ shiftDistance S P u := by
  unfold shiftDistance
  apply mul_nonneg
  · simp
  exact Finset.sum_nonneg fun x _ => abs_nonneg _

/-- Δ(P, u) = 0 quand `P` s'annule sur `S` **et** sur sa translatée
`S + u` : chaque terme `|P (x + u) − P x|` de la somme est alors nul, et
la somme entière vaut 0, donc `½ · 0 = 0`.

L'obstacle annoncé à la brique k1.1 (« la preuve directe est delicate en
Lean 4 v4.33.0 ») portait sur une réécriture globale de la somme ; il se
lève terme à terme : `Finset.sum_eq_zero` suffit, la somme est nulle dès
que chaque terme l'est. -/
lemma shiftDistance_eq_zero_of_zero {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ)
    (hS : ∀ x ∈ S, P x = 0) (hSu : ∀ x ∈ S, P (x + u) = 0) :
    shiftDistance S P u = 0 := by
  unfold shiftDistance
  have hsum : ∑ x ∈ S, |P (x + u) - P x| = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [hSu x hx, hS x hx]
  rw [hsum, mul_zero]

/-- Δ(P, u) = 0 dès que `P` est **invariante** par le décalage `u` sur
`S` : le terme `|P (x + u) − P x|` vaut alors `|P x − P x| = 0`.

Condition suffisante distincte de `shiftDistance_eq_zero_of_zero` (qui
suppose `P` identiquement nulle sur `S ∪ (S + u)`) : les deux se
combinent, aucune ne se déduit de l'autre. -/
lemma shiftDistance_eq_zero_of_invariant {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ)
    (h : ∀ x ∈ S, P (x + u) = P x) :
    shiftDistance S P u = 0 := by
  unfold shiftDistance
  have hsum : ∑ x ∈ S, |P (x + u) - P x| = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [h x hx]
  rw [hsum, mul_zero]

/-! **Reporté à c.886+** : 2 briques **non closes** dans ce commit, à
livrer dans un module **aval de `Split.lean`** (k1.2) — l'organe de
ré-indexation `sum_translate_image` y est disponible, alors que
`Split.lean` dépend du présent module (dépendance circulaire non
inversible) :

1. `shiftDistance_symm` — Δ(u) = Δ(−u) exige l'hypothèse d'invariance
   du support (`S = S.image (· + u)`) **et** la ré-indexation de la somme
   par `−u`. Sans la première, le lemme est faux en général :
   `|P (x + u) − P x| ≠ |P (x − u) − P x|` pour P asymétrique.

2. `shiftDistance_le_one` — Δ(P, u) ≤ ½ · ‖P‖₁ par inégalité
   triangulaire, donc Δ ≤ 1 sous masse 1. Deux conditions distinctes :
   `|P (x + u) − P x| ≤ P (x + u) + P x` sous positivité de `P`, et le
   report de la masse `∑_{x ∈ S} P (x + u) = ∑_{x ∈ S} P x` — c'est-à-dire
   l'organe `sum_translate_image` de `Split.lean`.

Briques closes dans ce commit : `shiftDistance`, `shiftDistance_zero`,
`shiftDistance_nonneg`, `shiftDistance_eq_zero_of_zero`,
`shiftDistance_eq_zero_of_invariant`. Le module build
(`lake build Discrepancy.Komlos.ShiftDistance` SUCCESS attendu), 0
`sorry` en code. -/

end Discrepancy.Komlos
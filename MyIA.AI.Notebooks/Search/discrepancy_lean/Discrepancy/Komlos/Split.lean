/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/Split.lean`, toolchain v4.34.0, cadre `Finsupp` sur `E →₀ ℝ`,
hauteur `E × ℝ`). L'adaptation ci-dessous suit la convention du lake
établie par la brique k1.1 (`ShiftDistance.lean`) : cadre **Finset
explicite** `P : (Fin d → ℤ) → ℝ` avec support `S` passé en argument, et
hauteur `Bool` (`false` = tranche 0, `true` = tranche 1) — fidèle au
« support fini » du papier, sans `Fintype` artificiels ni `Module`
superflus.

**Portée de ce commit** (brique k1.2, `lake build SUCCESS` requis, 0
`sorry`) :

Briques closes : `split` (Def 3.1), `split_apply_zero`, `split_apply_one`,
`split_nonneg`, `sum_invariance_image` (ré-indexation d'une somme sous
invariance `S.image f = S` pour `f` injective — la brique réutilisable qui
manquait à `shiftDistance_symm`, reportée de k1.1 ; cas additif
`sum_translate_image` pour k1.3), `split_mass` (la scission préserve
la masse — propriété structurelle qui fait de `T_v` une opération sur les
distributions), `split_mono` (monotonie ponctuelle).

**Reporté à k1.3+** : le Claim 3.2 (`shiftDist_split_le` chez Dahia :
`Δ(T_v P, (u, 0)) ≤ Δ(P, u)`) exige l'identité `Δ = 1 − overlap`, qui
exige elle-même l'opérateur `overlap` — non encore distillé dans ce lake ;
la commutation `split_tr` (scission ∘ translation) suit le même chemin.
L'état détaillé vit dans `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.ShiftDistance

/-!
# Opérateur de scission `T_v` (Def 3.1, Karingula–Lovett)

`Discrepancy.Komlos.split v P` est la distribution scindée sur
`(Fin d → ℤ) × Bool` : à hauteur `false` (tranche 0) elle assigne la
moitié du **maximum** de `P (x + v)` et `P (x - v)`, à hauteur `true`
(tranche 1) la moitié de leur **minimum**.

La scission préserve la masse (`split_mass`) : la moitié haute et la
moitié basse redistribuent exactement `P (x + v) + P (x - v)`, et la
ré-indexation `sum_invariance_image` télescope les deux sommes sous
l'hypothèse d'invariance du support par `±v` — l'hypothèse exacte que
k1.1 a identifiée comme nécessaire aux identités symétriques de `Δ`.

**Convention de hauteur** : `Bool` plutôt que `ℝ` (Dahia : tranches
`E × {0, 1}`) — les deux tranches du papier sont les deux valeurs du
booléen, aucun calcul sur la hauteur n'apparaît dans la preuve.

Cette brique ne suppose que `Komlos.ShiftDistance` (et transitivement
`Discrepancy.Basic`). Le pin Mathlib `db584cd6` est dans la cohorte fleet
v4.32.1 (mutualisation #4363) ; l'écart avec la toolchain locale v4.33.0
est pris en charge par `lake build`.
-/

namespace Discrepancy.Komlos

/-- Opérateur de scission `T_v` (Def 3.1) : à `(x, false)` la moitié du
maximum de `P (x + v)` et `P (x - v)`, à `(x, true)` la moitié du
minimum. C'est le remplaçant **fini** du réarrangement continu de
Guo–Fang–Lu : il découple les masses haute/basse sans jamais quitter le
registre des distributions à support fini. -/
noncomputable def split {d : ℕ} (v : Fin d → ℤ)
    (P : (Fin d → ℤ) → ℝ) : ((Fin d → ℤ) × Bool) → ℝ := fun y =>
  if y.2 then (1 / 2 : ℝ) * min (P (y.1 + v)) (P (y.1 - v))
  else (1 / 2 : ℝ) * max (P (y.1 + v)) (P (y.1 - v))

/-- Tranche 0 : `(T_v P)(x, false) = ½ · max{P (x + v), P (x - v)}`. -/
lemma split_apply_zero {d : ℕ} (v : Fin d → ℤ) (P : (Fin d → ℤ) → ℝ)
    (x : Fin d → ℤ) :
    split v P (x, false) = (1 / 2 : ℝ) * max (P (x + v)) (P (x - v)) := by
  simp [split]

/-- Tranche 1 : `(T_v P)(x, true) = ½ · min{P (x + v), P (x - v)}`. -/
lemma split_apply_one {d : ℕ} (v : Fin d → ℤ) (P : (Fin d → ℤ) → ℝ)
    (x : Fin d → ℤ) :
    split v P (x, true) = (1 / 2 : ℝ) * min (P (x + v)) (P (x - v)) := by
  simp [split]

/-- La scission d'une fonction positive reste positive : chaque tranche
porte une moitié de max/min de valeurs positives. -/
lemma split_nonneg {d : ℕ} {P : (Fin d → ℤ) → ℝ} (hP : ∀ x, 0 ≤ P x)
    (v : Fin d → ℤ) (y : (Fin d → ℤ) × Bool) : 0 ≤ split v P y := by
  obtain ⟨x, b⟩ := y
  cases b with
  | false =>
    rw [split_apply_zero]
    exact mul_nonneg (by norm_num)
      ((hP (x + v)).trans (le_max_left (P (x + v)) (P (x - v))))
  | true =>
    rw [split_apply_one]
    exact mul_nonneg (by norm_num) (le_min (hP _) (hP _))

/-- Ré-indexation d'une somme sous invariance d'image : si `f` est injective
et préserve le support (`S.image f = S`), sommer `P (f x)` sur `S` revient
à sommer `P` sur `S`. C'est la brique de télescopage qui manquait à
`shiftDistance_symm` (reportée de k1.1) : l'invariance du support, et non
la seule inclusion, est ce qui rend la ré-indexation exacte pour un `P`
arbitraire. Forme générique — `sum_translate_image` en est le cas additif. -/
lemma sum_invariance_image {d : ℕ} {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)} {f : (Fin d → ℤ) → (Fin d → ℤ)}
    (hf : ∀ a b, f a = f b → a = b) (hS : S.image f = S) :
    ∑ x ∈ S, P (f x) = ∑ x ∈ S, P x := by
  have hinj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b :=
    fun a _ b _ hab => hf a b hab
  calc ∑ x ∈ S, P (f x)
      = ∑ y ∈ S.image f, P y := (Finset.sum_image hinj).symm
    _ = ∑ y ∈ S, P y := by rw [hS]

/-- Cas additif `f = (· + u)` : la forme sous laquelle k1.3 réutilisera la
ré-indexation pour les identités symétriques de `Δ`. -/
lemma sum_translate_image {d : ℕ} (u : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)} (hS : S.image (fun x => x + u) = S) :
    ∑ x ∈ S, P (x + u) = ∑ x ∈ S, P x :=
  sum_invariance_image (f := fun x => x + u) (fun _ _ hab => add_right_cancel hab) hS

/-- La scission préserve la masse (Claim implicite du papier, `mass_split`
chez Dahia) : sous invariance du support par `±v`, la masse totale de
`T_v P` sur `S × {false, true}` égale la masse de `P` sur `S`. C'est la
propriété structurelle qui fait de `T_v` une opération sur les
distributions plutôt qu'une simple fonction. -/
lemma split_mass {d : ℕ} (v : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hSv : S.image (fun x => x + v) = S)
    (hSvm : S.image (fun x => x - v) = S) :
    ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool), split v P y = ∑ x ∈ S, P x := by
  have key : ∀ x ∈ S, split v P (x, false) + split v P (x, true)
      = (P (x + v) + P (x - v)) * (1 / 2 : ℝ) := by
    intro x _
    rw [split_apply_zero, split_apply_one, ← mul_add, max_add_min, mul_comm]
  have hbool : ∀ x ∈ S, ∑ y ∈ (Finset.univ : Finset Bool), split v P (x, y)
      = split v P (x, false) + split v P (x, true) := by
    intro x _
    simp; ac_rfl
  have hsub : ∀ a b : Fin d → ℤ, a - v = b - v → a = b := by
    intro a b hab
    have h2 : a - v + v = b - v + v := by rw [hab]
    simpa [sub_add_cancel] using h2
  rw [Finset.sum_product, Finset.sum_congr rfl hbool,
    Finset.sum_congr rfl key, ← Finset.sum_mul, Finset.sum_add_distrib,
    sum_invariance_image (f := fun x => x + v) (fun a b hab => add_right_cancel hab) hSv,
    sum_invariance_image (f := fun x => x - v) hsub hSvm]
  linarith

/-- Monotonie ponctuelle de la scission (`split_mono` chez Dahia) : si
`P ≤ Q` ponctuellement, alors `T_v P ≤ T_v Q` ponctuellement — le max et
le min se transportent par monotonie, la hauteur est inchangée. -/
lemma split_mono {d : ℕ} (v : Fin d → ℤ) {P Q : (Fin d → ℤ) → ℝ}
    (h : ∀ x, P x ≤ Q x) (y : (Fin d → ℤ) × Bool) :
    split v P y ≤ split v Q y := by
  obtain ⟨x, b⟩ := y
  cases b with
  | false =>
    rw [split_apply_zero, split_apply_zero]
    exact mul_le_mul_of_nonneg_left (max_le_max (h _) (h _)) (by norm_num)
  | true =>
    rw [split_apply_one, split_apply_one]
    exact mul_le_mul_of_nonneg_left (min_le_min (h _) (h _)) (by norm_num)

end Discrepancy.Komlos

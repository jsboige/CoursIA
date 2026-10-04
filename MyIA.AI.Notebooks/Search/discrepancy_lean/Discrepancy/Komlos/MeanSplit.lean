/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/Split.lean`, toolchain v4.34.0, cadre `Finsupp` sur `E →₀ ℝ`,
hauteur `E × ℝ`). L'adaptation ci-dessous suit la convention du lake établie
par la brique k1.1 (`ShiftDistance.lean`) : cadre **Finset explicite** avec
support en argument, hauteur `Bool` pour l'espace produit (k1.2).

**Portée de ce commit** (brique k2.0, `lake build SUCCESS` requis, 0 `sorry`) :

Briques closes : `coordMoment` et `prodMoment` (les **moments** — barycentre
coordonnée par coordonnée, sur la base et sur l'espace produit),
`heightMoment` (le moment de hauteur), `heightMoment_split` (le moment de
hauteur de `T_v P` est le bit de scission), `prodMoment_split` (la scission
**préserve** le moment de base), et `mean_split` — la forme lake de
`mean_split` chez Dahia, **l'item que k1.6 a explicitement reporté à k2**.

**Pourquoi cette brique est un préalable à k2 et non un ornement.** Le
`mean_split` de Dahia s'énonce sur un `Finsupp` de `E × ℝ` :
`mean (split v P) = (mean P, splitBit v P)`, avec `mean P = ∑_x P x • x`. Ce
cadre n'existe pas dans ce lake : `x : Fin d → ℤ` n'est pas un `ℝ`-module, la
scalarisation `P x • x` n'a pas de sens. La décomposition fidèle est donc
**par composante** — et c'est ce que ce module livre :

- la composante de **hauteur** `∑_y (T_v P)(y) · (y.2)` vaut `splitBit v P S`
  (généralisation de `sum_split_high` de k1.6 à la pondération par la hauteur) ;
- la composante de **base** `∑_y (T_v P)(y) · (y.1 i)` vaut le moment de `P`
  en la coordonnée `i` — la scission **conserve le barycentre**, ce qui n'était
  pas dit par `split_mass` (qui ne conserve que la masse, moment d'ordre 0).

C'est cette conservation du moment d'ordre 1 qui porte l'énoncé de k2 : le
Lemme 1.4 conclut `μ(P) + ∑ ε_i v_i ∈ conv(supp P)`, une affirmation sur le
**barycentre**, pas sur la masse.

**Reporté à k2 (Lemma 1.4)** : le lemme d'entropie et l'induction simultanée
sur `n` et `d`. L'état détaillé vit dans `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.SplitBit

/-!
# Moments de la scission et `mean_split` (Karingula–Lovett)

Ce module ferme l'identité `mean_split` — la moyenne de `T_v P` sous ses deux
composantes : le barycentre de base est **conservé** par la scission, et le
moment de hauteur **est** le bit de scission. C'est l'ingrédient d'ordre 1 que
le Lemma 1.4 consomme, là où les briques k1 ne fournissaient que le moment
d'ordre 0 (`split_mass`).

**Convention de lecture.** L'oracle Dahia écrit `mean (split v P) = (mean P,
splitBit v P)` dans un cadre `E` réel où `P x • x` a un sens. Ici la base est
`Fin d → ℤ` : le moment est donc lu **coordonnée par coordonnée** (`i : Fin d`),
chaque coordonnée étant poussée dans `ℝ` par `(x i : ℝ)`. Aucune structure de
module réel n'est requise sur la base — c'est l'adaptation du cadre, déclarée
plutôt que contournée par un `Fintype` ou un plongement artificiels.

**Hypothèses.** `prodMoment_split` requiert l'invariance du support par `±v`
— les mêmes hypothèses que `split_mass` (k1.2), et pour la même raison : la
ré-indexation `x ↦ x ± v` doit être exacte sur `S`. `heightMoment_split`
n'en requiert aucune : le moment de hauteur se lit tranche par tranche.
-/

namespace Discrepancy.Komlos

/-- **Moment coordonné** (barycentre) d'une distribution `P` sur son support
`S`, en la coordonnée `i` : `∑ x ∈ S, P x * (x i : ℝ)`. C'est l'analogue
coordonnée du `mean P = ∑_x P x • x` de Dahia — la base du lake étant
`Fin d → ℤ` (pas un `ℝ`-module), le moment se lit coordonnée par coordonnée,
chaque coordonnée poussée dans `ℝ`. -/
noncomputable def coordMoment {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) (i : Fin d) : ℝ :=
  ∑ x ∈ S, P x * (x i : ℝ)

/-- **Moment de hauteur** d'une distribution sur l'espace produit
`(Fin d → ℤ) × Bool` : `∑ y ∈ T, P y * (y.2 : ℝ)`, la hauteur `Bool` étant
lue `false ↦ 0`, `true ↦ 1`. C'est la composante de hauteur du `mean` de
Dahia, dont le second facteur est `r : ℝ` dans son cadre `E × ℝ`. -/
noncomputable def heightMoment {d : ℕ} (P : ((Fin d → ℤ) × Bool) → ℝ)
    (T : Finset ((Fin d → ℤ) × Bool)) : ℝ :=
  ∑ y ∈ T, P y * (if y.2 then (1 : ℝ) else 0)

/-- **Moment de base** d'une distribution sur l'espace produit, en la
coordonnée `i` : `∑ y ∈ T, P y * (y.1 i : ℝ)`. Composante de base du `mean`
de Dahia (`x • x` remplacé par la lecture coordonnée, cf `coordMoment`). -/
noncomputable def prodMoment {d : ℕ} (P : ((Fin d → ℤ) × Bool) → ℝ)
    (T : Finset ((Fin d → ℤ) × Bool)) (i : Fin d) : ℝ :=
  ∑ y ∈ T, P y * (y.1 i : ℝ)

/-- **Le moment de hauteur de la scission est le bit de scission** :
`∑_y (T_v P)(y) · (y.2) = splitBit v P S`. Généralise `sum_split_high` (k1.6)
— qui est le cas sans pondération — à la lecture de hauteur : la tranche
`false` porte le poids `0`, la tranche `true` le poids `1`, et il ne reste que
la masse de la tranche haute. Aucune invariance du support n'est requise. -/
lemma heightMoment_split {d : ℕ} (v : Fin d → ℤ) (P : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) :
    heightMoment (split v P) (S ×ˢ (Finset.univ : Finset Bool)) = splitBit v P S := by
  have hbool : ∀ x : Fin d → ℤ,
      (∑ b ∈ (Finset.univ : Finset Bool), split v P (x, b) * (if b then (1 : ℝ) else 0))
        = split v P (x, true) := by
    intro x
    simp
  rw [heightMoment, Finset.sum_product,
    Finset.sum_congr rfl fun x _ => hbool x]
  exact sum_split_high v P S

/-- **La scission conserve le moment de base** : `∑_y (T_v P)(y) · (y.1 i)`
vaut le moment coordonné de `P` en `i`. C'est l'énoncé d'ordre 1 que
`split_mass` (k1.2, ordre 0) ne portait pas, et la composante de base de
`mean_split`. Preuve : par `x` fixé, les deux tranches se somment en
`½(P(x+v) + P(x−v))` (l'identité `max_add_min` déjà consommée par
`split_mass`), puis les deux termes se ré-indexent par `x ↦ x ∓ v`
(`sum_translate_image`, k1.2) et redeviennent les deux moitiés du même moment
`((x−v) i) + ((x+v) i) = 2 · (x i)`. -/
lemma prodMoment_split {d : ℕ} (v : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hSv : S.image (fun x => x + v) = S)
    (hSvm : S.image (fun x => x - v) = S) (i : Fin d) :
    prodMoment (split v P) (S ×ˢ (Finset.univ : Finset Bool)) i
      = coordMoment P S i := by
  have hbool : ∀ x : Fin d → ℤ,
      (∑ b ∈ (Finset.univ : Finset Bool), split v P (x, b)) * (x i : ℝ)
        = (1 / 2 : ℝ) * (P (x + v) + P (x - v)) * (x i : ℝ) := by
    intro x
    have h2 : (∑ b ∈ (Finset.univ : Finset Bool), split v P (x, b))
        = split v P (x, false) + split v P (x, true) := by
      simp
      ac_rfl
    rw [h2, split_apply_zero, split_apply_one, ← mul_add, max_add_min]
  have hreindex_plus : ∑ x ∈ S, (1 / 2 : ℝ) * P (x + v) * (x i : ℝ)
      = ∑ x ∈ S, (1 / 2 : ℝ) * P x * (((x - v) i : ℤ) : ℝ) := by
    have h := sum_translate_image v hSv
      (P := fun x => (1 / 2 : ℝ) * P x * (((x - v) i : ℤ) : ℝ))
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : ((x + v) - v) i = x i := by simp [Pi.sub_apply, Pi.add_apply]
    rw [this]
  have hreindex_minus : ∑ x ∈ S, (1 / 2 : ℝ) * P (x - v) * (x i : ℝ)
      = ∑ x ∈ S, (1 / 2 : ℝ) * P x * (((x + v) i : ℤ) : ℝ) := by
    have h := sum_translate_image (-v) hSvm
      (P := fun x => (1 / 2 : ℝ) * P x * (((x + v) i : ℤ) : ℝ))
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hkey : (((x + -v) + v) i : ℤ) = x i := by
      simp [Pi.add_apply]
    rw [hkey]
    have hx : x + -v = x - v := by
      funext j
      simp [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg]
    rw [hx]
  have hinner : ∀ x ∈ S,
      (∑ b ∈ (Finset.univ : Finset Bool), split v P (x, b) * (x i : ℝ))
        = (1 / 2 : ℝ) * (P (x + v) + P (x - v)) * (x i : ℝ) := by
    intro x _
    rw [← Finset.sum_mul]
    exact hbool x
  have hsplit : ∀ x ∈ S,
      (1 / 2 : ℝ) * (P (x + v) + P (x - v)) * (x i : ℝ)
        = (1 / 2 : ℝ) * P (x + v) * (x i : ℝ)
          + (1 / 2 : ℝ) * P (x - v) * (x i : ℝ) := by
    intro x _
    ring
  unfold prodMoment coordMoment
  rw [Finset.sum_product]
  rw [Finset.sum_congr rfl hinner, Finset.sum_congr rfl hsplit,
    Finset.sum_add_distrib, hreindex_plus, hreindex_minus,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply, Int.cast_sub, Int.cast_add]
  ring

/-- **`mean_split`** (forme lake de `mean_split` chez Dahia) : la moyenne de
`T_v P` sur `S × {false, true}` vaut, composante par composante, le couple
`(moment de base de P, bit de scission)`. C'est l'identité d'ordre 1 que le
Lemme 1.4 consomme : `splitBit` porte l'information de la scission vers la
distance de translation (k1.6), le moment de base porte le barycentre vers la
conclusion `μ(P) + ∑ ε_i v_i ∈ conv(supp P)`. -/
theorem mean_split {d : ℕ} (v : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hSv : S.image (fun x => x + v) = S)
    (hSvm : S.image (fun x => x - v) = S) (i : Fin d) :
    (prodMoment (split v P) (S ×ˢ (Finset.univ : Finset Bool)) i,
      heightMoment (split v P) (S ×ˢ (Finset.univ : Finset Bool)))
      = (coordMoment P S i, splitBit v P S) := by
  rw [prodMoment_split v hSv hSvm i, heightMoment_split v P S]

end Discrepancy.Komlos

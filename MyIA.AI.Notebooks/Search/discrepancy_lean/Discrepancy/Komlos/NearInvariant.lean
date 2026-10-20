/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` : `Komlos/NearInvariant.lean`
(Lemme 1.5, `exists_nearInvariant`). L'adaptation reprend le module **nom pour nom**
dans le cadre Finset explicite du lake (convention k1.1) — voir la portée ci-dessous.

**Portée de ce commit** (brique k4.3, `lake build SUCCESS` requis, 0 `sorry`) :

Briques closes : `gridEmb` + `gridEmb_apply` + `gridEmb_injective` (le plongement
`g ↦ g / N` de la grille entière dans `N⁻¹ • ℤ^d` — chez l'oracle l.28-43),
`gridF_neg` / `cubeF_neg` (les deux identités de parité du poids produit),
`nearBox` + `nearBox_neg` (la boîte de travail **uniforme** de ce module),
`shiftDistance_nearBox_eq_shiftBox` + `shiftDistance_cubeF_sq_le_nearBox` (la borne
quadratique de k4.2 relue sur cette boîte uniforme), puis `exists_nearInvariant`
(le Lemme 1.5 lui-même).

**La difficulté propre du port, et comment elle se résout.** Chez l'oracle, `P` est un
`Finsupp` : son support est **canonique**, et son `shiftDist P u` somme sur le support
de `P - tr u P` — donc sur l'union des deux supports translatés, automatiquement. Dans
le lake, la `Finset` de sommation est un **paramètre** (k1.1) et le support de l'énoncé
est **existentiel** : la même `Finset` doit donc servir les **tous** les décalages `g`
de la conclusion, alors que la boîte de k4.2 (`shiftBox N h`) dépend de `h`. C'est
`nearBox d N` qui les réconcilie : la boîte `[-7N, 7N]^d`, qui contient `shiftBox N h`
**pour tout** `h` admissible (`|h k| ≤ N`, conséquence de l'hypothèse
`Σ k, ((h k)/N)² ≤ 1`), et où les contributions hors support sont nulles — la somme y
**est** la distance de décalage (contrat de k1.1 : « `S` peut être plus large que
nécessaire »), et elle coïncide terme à terme avec celle de `shiftBox`
(`shiftDistance_nearBox_eq_shiftBox`).

**Ce que le lake paie, et où.** Le vocabulaire `IsDist` de l'oracle reste hors du lake
(décision de cadre k1.1) : `exists_nearInvariant` le rend **en clair** dans sa
conclusion — positivité ponctuelle, masse 1, support à `‖x‖ ≤ 6`, moyenne nulle —
comme k2.5 l'avait fait pour `mean_mem_convexHull`. La moyenne nulle se lit
coordonnée par coordonnée (`coordMomentReal`, k2.3) : la grille réelle n'a pas de
`mean` vectoriel dans ce lake, elle a des moments, et l'annulation de chacun est
l'énoncé « moyenne nulle ». Le lemme générique de l'oracle (`sum_smul_eq_zero_of_neg`)
n'est pas porté tel quel : sa forme `Finsupp` (`equivMapDomain`, `Finsupp.sum_neg`)
n'a pas d'objet dans un lake sans `Finsupp` — sa **substance** (un poids pair sur une
boîte symétrique a un moment nul) est prouvée directement, par ré-indexation
`Finset.sum_map` sur la négation.

**Reporté, avec raison mesurée** : rien. Le module oracle est porté **en intégralité**.
`IsDist.push` (reporté par k2.3, k4.2c) reste le seul vocabulaire non payé du
transport, et il n'a **toujours pas** de consommateur : k4.3 rend ses composantes en
clair plutôt que de le payer.

**Consommé par** : la suite de la campagne (assemblage du théorème d'écart,
EPIC #17845).
-/

import Discrepancy.Komlos.Cube
import Discrepancy.Komlos.ShiftPush
import Discrepancy.Komlos.Transport

/-!
# Distributions quasi-invariantes (brique k4.3, Lemme 1.5)

Pour tout `N > 0` il existe une distribution `P` sur la grille réelle
`N⁻¹ • ℤ^d` — positive, de masse `1`, supportée dans `[-6, 6]^d`, de **moyenne
nulle** — telle que pour **tout** `g : Fin d → ℤ` de décalage normalisé de norme au
plus `1` (`Σ k, ((g k)/N)² ≤ 1`), la distance de décalage entre `P` et son translaté
par `g / N` est au plus `1/3`.

C'est le Lemme 1.5 de Karingula–Lovett, et c'est la brique qui **consomme toute la
campagne k4** : `cubeF d N ^ 2` (k4.2) est le poids produit dont le décalage est
quadratiquement petit, `gridEmb d N` (`g ↦ g / N`) est le plongement que k4.2c
transporte, et `shiftDistanceTV_push` relit la borne de `Komlos.Cube` sur la grille
réelle **sans la recalculer**.

La preuve tient en trois gestes : (1) pousser `cubeF d N ^ 2` le long de
`gridEmb d N` (`push`, k2.3) ; (2) lire les invariants de la poussée sur les organes
déjà livrés — positivité et masse (`push_apply`, `push_mass`), support
(`support_gridF_subset`), moyenne nulle par **symétrie** (le poids produit est pair,
la boîte est symétrique) ; (3) borner le décalage en transportant
`shiftDistance_cubeF_sq_le` (k4.2) sur la boîte uniforme `nearBox`, puis par
`shiftDistanceTV_push` (k4.2c). Le `IsDist` de l'oracle n'est pas payé : la
conclusion l'écrit en clair, comme le lake l'écrit partout.
-/

namespace Discrepancy.Komlos

open Finset

/-- **Plongement de la grille entière dans la grille réelle** : `gridEmb d N g` est
la fonction `k ↦ (g k : ℝ) / N`, c'est-à-dire le point `g / N` de `N⁻¹ • ℤ^d`.

C'est le plongement sous lequel k4.3 transporte le poids produit — chez l'oracle
(`Komlos/NearInvariant.lean` l.28-35) `gridEmb d N g k = (g k : ℝ) / N`. Additif
coordonnée par coordonnée ; injectif pour `N > 0` (`gridEmb_injective`). Il compose
`toReal` (k2.3) avec l'homothétie `· / N`, comme l'annonçait `Transport.lean`. -/
noncomputable def gridEmb (d N : ℕ) : (Fin d → ℤ) →+ (Fin d → ℝ) where
  toFun g k := (g k : ℝ) / N
  map_zero' := by ext k; simp
  map_add' g g' := by
    ext k
    simp only [Pi.add_apply, Int.cast_add, add_div]

/-- Lecture coordonnée du plongement : `gridEmb d N g k = (g k : ℝ) / N`. -/
@[simp] lemma gridEmb_apply (d N : ℕ) (g : Fin d → ℤ) (k : Fin d) :
    gridEmb d N g k = (g k : ℝ) / N := rfl

/-- **Le plongement est injectif** pour `N > 0` : l'égalité des images donne
l'égalité des quotients `(g k)/N`, donc — le dénominateur étant non nul — l'égalité
des coordonnées entières. (Chez l'oracle : `gridEmb_injective`, l.31-33.) -/
lemma gridEmb_injective {d N : ℕ} (hN : 0 < N) : Function.Injective (gridEmb d N) := by
  intro g g' h
  funext k
  have hk := congrFun h k
  simp only [gridEmb_apply] at hk
  exact Int.cast_injective
    ((div_left_inj' (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0)).mp hk)

/-- Le poids unidimensionnel est **pair** : `gridF N (-j) = gridF N j`. C'est la
parité de la tente (`tent_neg`, k3.1) telle que la lit la grille. -/
lemma gridF_neg (N : ℕ) (j : ℤ) : gridF N (-j) = gridF N j := by
  simp [gridF]

/-- Le poids produit est **pair** : `cubeF d N (-g) = cubeF d N g` — produit de
facteurs pairs. (Chez l'oracle : `cubeP_neg`.) -/
lemma cubeF_neg {d N : ℕ} (g : Fin d → ℤ) : cubeF d N (-g) = cubeF d N g := by
  simp only [cubeF]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.neg_apply, gridF_neg]

/-- **La boîte de travail uniforme** de k4.3 : `[-7N, 7N]^d`, c'est-à-dire
`(Icc (-(gridM N + N)) (gridM N + N))^d`.

C'est la boîte qui rend le support de `exists_nearInvariant` **indépendant du
décalage** : elle contient `shiftBox N h` pour tout `h` dont les coordonnées
vérifient `|h k| ≤ N` — le cas de tout `h` admissible au sens de l'hypothèse
`Σ k, ((h k)/N)² ≤ 1`. Là où `shiftBox N h` suit le décalage, `nearBox` le majore
une fois pour toutes. `noncomputable` comme `shiftBox` (k4.2a) : un `Icc` de `ℤ`
n'est pas un calcul, c'est un intervalle de l'ordre non calculable. -/
noncomputable def nearBox (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d ↦ Icc (-(((gridM N + N : ℕ) : ℤ))) ((gridM N + N : ℕ) : ℤ)

/-- **La boîte uniforme est symétrique** : `nearBox d N` est stable par négation —
c'est ce que la moyenne nulle consomme. Chaque coordonnée vit dans un `Icc` centré
en `0`, donc l'appartenance y **est** une majoration de la valeur absolue (`abs_le`) ;
la valeur absolue est invariante par négation (`abs_neg`), et la stabilité suit
coordonnée par coordonnée. -/
lemma nearBox_neg {d N : ℕ} :
    (nearBox d N).map ⟨Neg.neg, neg_injective⟩ = nearBox d N := by
  have hB : ∀ x : Fin d → ℤ,
      (x ∈ nearBox d N ↔ ∀ k, |x k| ≤ (((gridM N + N : ℕ) : ℤ))) := by
    intro x
    rw [nearBox, Fintype.mem_piFinset]
    constructor
    · intro h k
      have hk := h k
      rw [Finset.mem_Icc] at hk
      exact abs_le.mpr hk
    · intro h k
      rw [Finset.mem_Icc]
      exact abs_le.mp (h k)
  ext x
  rw [Finset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (-y) ∈ nearBox d N
    exact (hB (-y)).mpr (by
      intro k
      show |(-y) k| ≤ (((gridM N + N : ℕ) : ℤ))
      rw [Pi.neg_apply, abs_neg]
      exact (hB y).mp hy k)
  · intro hx
    exact ⟨-x, (hB (-x)).mpr (by
      intro k
      show |(-x) k| ≤ (((gridM N + N : ℕ) : ℤ))
      rw [Pi.neg_apply, abs_neg]
      exact (hB x).mp hx k), neg_neg x⟩

/-- **La somme de décalage sur la boîte uniforme est celle sur la boîte de k4.2**,
dès que le décalage est admissible (`|h k| ≤ N`) : les deux boîtes contiennent le
support de `cubeF d N ^ 2` **et** celui de son translaté, et le contrat de k1.1
(« `S` peut être plus large que nécessaire ») fait que les contributions
supplémentaires sont nulles.

C'est la pièce qui rend le support de `exists_nearInvariant` uniforme : `nearBox`
majore `shiftBox N h` pour **tout** `h` admissible, et la valeur de la distance n'en
change pas. La somme sur `shiftBox` est la borne de k4.2 ; celle sur `nearBox` est
celle que le transport lit. -/
lemma shiftDistance_nearBox_eq_shiftBox {d N : ℕ} (h : Fin d → ℤ)
    (hh : ∀ k, |h k| ≤ (N : ℤ)) :
    shiftDistance (nearBox d N) (fun g ↦ cubeF d N g ^ 2) (-h)
      = shiftDistance (Fintype.piFinset fun _ : Fin d ↦ shiftBox N h)
          (fun g ↦ cubeF d N g ^ 2) (-h) := by
  have hcast : (((gridM N + N : ℕ) : ℤ)) = (gridM N : ℤ) + (N : ℤ) := by
    push_cast
    ring
  have hsub : (Fintype.piFinset fun _ : Fin d ↦ shiftBox N h) ⊆ nearBox d N := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    rw [nearBox, Fintype.mem_piFinset]
    intro k
    have hk := hx k
    rw [shiftBox] at hk
    rw [Finset.mem_union] at hk
    rw [hcast, Finset.mem_Icc, ← abs_le]
    rcases hk with hk | hk
    · rw [Finset.mem_Icc] at hk
      calc |x k| ≤ (gridM N : ℤ) := abs_le.mpr hk
        _ ≤ (gridM N : ℤ) + (N : ℤ) := le_add_of_nonneg_right (Int.natCast_nonneg N)
    · rw [Finset.mem_biUnion] at hk
      obtain ⟨k', -, hk'⟩ := hk
      rw [Finset.mem_map] at hk'
      obtain ⟨a, ha, hax⟩ := hk'
      rw [Finset.mem_Icc] at ha
      have hax' : a + h k' = x k := by simpa using hax
      rw [← hax']
      calc |a + h k'| ≤ |a| + |h k'| := abs_add_le _ _
        _ ≤ (gridM N : ℤ) + (N : ℤ) :=
            add_le_add (abs_le.mpr ha) (hh k')
  have hzero : ∀ x ∈ nearBox d N,
      x ∉ Fintype.piFinset (fun _ : Fin d ↦ shiftBox N h) →
      |(fun g ↦ cubeF d N g ^ 2) (x + -h) - (fun g ↦ cubeF d N g ^ 2) x| = 0 := by
    intro x _ hxnot
    obtain ⟨k, hk⟩ : ∃ k, x k ∉ shiftBox N h := by
      by_contra hcon
      have hcon' : ∀ k, x k ∈ shiftBox N h := fun k => by
        by_contra hk
        exact hcon ⟨k, hk⟩
      exact hxnot (by rw [Fintype.mem_piFinset]; exact hcon')
    have hlt : (gridM N : ℤ) < |x k| := by
      by_contra hle
      have hle' : |x k| ≤ (gridM N : ℤ) := not_lt.mp hle
      exact hk (by
        rw [shiftBox]
        exact Finset.mem_union.mpr
          (Or.inl (by rw [Finset.mem_Icc]; exact abs_le.mp hle')))
    have hFx : cubeF d N x = 0 := by
      rw [cubeF]
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      by_contra hne
      have hmem := support_gridF_subset N hne
      have hcoord : -(gridM N : ℤ) ≤ x k ∧ x k ≤ (gridM N : ℤ) := by
        simpa only [Finset.mem_coe, Finset.mem_Icc] using hmem
      exact absurd (abs_le.mpr hcoord) (not_le.mpr hlt)
    have hFx' : cubeF d N (x + -h) = 0 := by
      rw [cubeF]
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      have harg : (x + -h) k = x k - h k := by
        rw [Pi.add_apply, Pi.neg_apply]
        ring
      rw [harg]
      by_contra hne
      have hmem := support_gridF_subset N hne
      exact hk (by
        rw [shiftBox]
        refine Finset.mem_union.mpr (Or.inr ?_)
        rw [Finset.mem_biUnion]
        exact ⟨k, Finset.mem_univ k, by
          rw [Finset.mem_map]
          exact ⟨x k - h k, by simpa only [Finset.mem_coe] using hmem, by simp⟩⟩)
    simp [hFx, hFx']
  have hsum : (∑ x ∈ Fintype.piFinset (fun _ : Fin d ↦ shiftBox N h),
      |(fun g ↦ cubeF d N g ^ 2) (x + -h) - (fun g ↦ cubeF d N g ^ 2) x|)
      = ∑ x ∈ nearBox d N,
          |(fun g ↦ cubeF d N g ^ 2) (x + -h) - (fun g ↦ cubeF d N g ^ 2) x| :=
    Finset.sum_subset hsub hzero
  unfold shiftDistance
  rw [hsum]

/-- **La borne quadratique de k4.2, sur la boîte uniforme** : pour tout décalage
admissible `|h k| ≤ N`, le carré de la distance de décalage du poids produit est
borné par `(Σ k, ((h k)/N)²) / 12` sur `nearBox d N` — la boîte qui ne dépend pas de
`h`.

C'est la forme que le transport de k4.3 consomme : `shiftDistance_cubeF_sq_le`
(k4.2) sur `shiftBox N h`, relue sur `nearBox` par
`shiftDistance_nearBox_eq_shiftBox`. -/
lemma shiftDistance_cubeF_sq_le_nearBox {d N : ℕ} (hN : 0 < N) {h : Fin d → ℤ}
    (hh : ∀ k, |h k| ≤ (N : ℤ)) :
    shiftDistance (nearBox d N) (fun g ↦ cubeF d N g ^ 2) (-h) ^ 2
      ≤ (∑ k, ((h k : ℝ) / N) ^ 2) / 12 := by
  rw [shiftDistance_nearBox_eq_shiftBox h hh]
  exact shiftDistance_cubeF_sq_le hN h

/-- **Lemme 1.5 (Karingula–Lovett), forme du lake** : pour `N > 0` il existe une
`Finset` `S` de la grille réelle et un poids `P` sur elle — positif, de masse `1`,
de support dans `[-6, 6]^d` (`∀ x, P x ≠ 0 → ‖x‖ ≤ 6`), de **moyenne nulle**
(`∀ i, coordMomentReal P S i = 0`) — tels que pour tout `g : Fin d → ℤ` de décalage
normalisé de norme au plus `1`, la distance de décalage entre `P` et son translaté
par `g / N` est au plus `1/3`.

Le poids est `cubeF d N ^ 2` poussé par `gridEmb d N` (`g ↦ g / N`), le support est
l'image de `nearBox d N` : les quatre premiers constituants se lisent sur les organes
k2.3 (`push_apply`, `push_mass`, le support de `Komlos.Grid`) et sur la symétrie
(`nearBox_neg`, `cubeF_neg`), le cinquième sur `shiftDistanceTV_push` (k4.2c) et la
borne de k4.2 relue sur `nearBox`.

Chez l'oracle, le premier constituant est `IsDist P` — un vocabulaire que ce lake
n'a pas (convention k1.1) : il est rendu ici en clair (positivité ponctuelle et
masse), comme la moyenne l'est coordonnée par coordonnée. -/
theorem exists_nearInvariant {d N : ℕ} (hN : 0 < N) :
    ∃ (S : Finset (Fin d → ℝ)) (P : (Fin d → ℝ) → ℝ),
      (∀ x ∈ S, 0 ≤ P x) ∧
      (∑ x ∈ S, P x) = 1 ∧
      (∀ x, P x ≠ 0 → ‖x‖ ≤ 6) ∧
      (∀ i, coordMomentReal P S i = 0) ∧
      ∀ g : Fin d → ℤ, (∑ k, ((g k : ℝ) / N) ^ 2) ≤ 1 →
        shiftDistanceTV S P (gridEmb d N g) ≤ 3⁻¹ := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set F : (Fin d → ℤ) → ℝ := fun g ↦ cubeF d N g ^ 2 with hF_def
  have he : Function.Injective (gridEmb d N) := gridEmb_injective hN
  refine ⟨(nearBox d N).map ⟨⇑(gridEmb d N), he⟩, push (gridEmb d N) F,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨g, -, rfl⟩ := hx
    show 0 ≤ push (gridEmb d N) F (gridEmb d N g)
    rw [push_apply (gridEmb d N) he F g, hF_def]
    exact sq_nonneg _
  · have hK : Function.support (gridF N) ⊆
        Icc (-(((gridM N + N : ℕ) : ℤ))) ((gridM N + N : ℕ) : ℤ) := by
      intro j hj
      have h1 : -(gridM N : ℤ) ≤ j ∧ j ≤ (gridM N : ℤ) := by
        simpa only [Finset.mem_coe, Finset.mem_Icc] using support_gridF_subset N hj
      have hcast : (((gridM N + N : ℕ) : ℤ)) = (gridM N : ℤ) + (N : ℤ) := by
        push_cast
        ring
      refine Finset.mem_coe.mpr ?_
      rw [Finset.mem_Icc, hcast]
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    rw [push_mass (gridEmb d N) he F (nearBox d N), hF_def]
    rw [nearBox]
    exact sum_cubeF_sq hN hK
  · intro x hx
    have hrange : ∃ g, gridEmb d N g = x := by
      by_contra hcon
      have hcon' : ∀ g, gridEmb d N g ≠ x := fun g hg => hcon ⟨g, hg⟩
      exact hx (push_eq_zero (gridEmb d N) F hcon')
    obtain ⟨g, rfl⟩ := hrange
    rw [push_apply (gridEmb d N) he F g] at hx
    have hgne : cubeF d N g ≠ 0 := by
      intro h0
      apply hx
      rw [hF_def]
      simp [h0]
    have hcoord : ∀ k, |g k| ≤ (gridM N : ℤ) := by
      intro k
      have hk : gridF N (g k) ≠ 0 := by
        intro h0
        exact hgne (by rw [cubeF]; exact Finset.prod_eq_zero (Finset.mem_univ k) h0)
      have hmem := support_gridF_subset N hk
      have hmem' : -(gridM N : ℤ) ≤ g k ∧ g k ≤ (gridM N : ℤ) := by
        simpa only [Finset.mem_coe, Finset.mem_Icc] using hmem
      exact abs_le.mpr hmem'
    refine (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)).mpr ?_
    intro k
    have h1 : |(g k : ℝ)| ≤ (gridM N : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast hcoord k
    rw [Real.norm_eq_abs, gridEmb_apply, abs_div, abs_of_nonneg hNpos.le,
      div_le_iff₀ hNpos]
    calc |(g k : ℝ)| ≤ (gridM N : ℝ) := h1
      _ = 6 * (N : ℝ) := cast_gridM N
  · intro i
    rw [coordMomentReal_push (gridEmb d N) he F (nearBox d N) i]
    have h1 : (∑ g ∈ nearBox d N, F g * gridEmb d N g i)
        = ∑ g ∈ nearBox d N, F (-g) * gridEmb d N (-g) i := by
      conv_lhs => rw [← nearBox_neg]
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl fun g _ => rfl
    have h2 : (∑ g ∈ nearBox d N, F (-g) * gridEmb d N (-g) i)
        = -∑ g ∈ nearBox d N, F g * gridEmb d N g i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun g _ => by
        have hFg : F (-g) = F g := by
          rw [hF_def]
          simp only [cubeF_neg]
        rw [hFg, map_neg, Pi.neg_apply]
        ring
    have h3 : (∑ g ∈ nearBox d N, F g * gridEmb d N g i)
        = -∑ g ∈ nearBox d N, F g * gridEmb d N g i := h1.trans h2
    linarith
  · intro g hg
    have hhk : ∀ k, |g k| ≤ (N : ℤ) := by
      intro k
      have h1 : ((g k : ℝ) / N) ^ 2 ≤ 1 :=
        le_trans (Finset.single_le_sum (f := fun k ↦ ((g k : ℝ) / N) ^ 2)
          (fun i _ ↦ sq_nonneg _) (Finset.mem_univ k)) hg
      have h1' : ((g k : ℝ) / N) ^ 2 ≤ (1 : ℝ) ^ 2 := by simpa using h1
      have h2 : |(g k : ℝ) / N| ≤ 1 := by simpa using sq_le_sq.mp h1'
      have h3 : |(g k : ℝ)| / (N : ℝ) ≤ 1 := by
        simpa [abs_div, abs_of_pos hNpos] using h2
      have h4 : |(g k : ℝ)| ≤ (N : ℝ) := by
        simpa using (div_le_iff₀ hNpos).mp h3
      have h5 : ((|g k| : ℤ) : ℝ) ≤ ((N : ℕ) : ℝ) := by
        rw [Int.cast_abs]
        exact h4
      exact_mod_cast h5
    have hb := shiftDistance_cubeF_sq_le_nearBox (d := d) (N := N) hN (h := -g)
      (fun k => by simpa using hhk k)
    rw [neg_neg] at hb
    have hsum : (∑ k, (((-g) k : ℝ) / N) ^ 2) = ∑ k, ((g k : ℝ) / N) ^ 2 := by
      refine Finset.sum_congr rfl fun k _ => by
        rw [Pi.neg_apply, Int.cast_neg]
        ring
    have hbound : (∑ k, ((g k : ℝ) / N) ^ 2) / 12 ≤ (3⁻¹ : ℝ) ^ 2 := by
      have hdiv : (∑ k, ((g k : ℝ) / N) ^ 2) / 12 ≤ 1 / 12 :=
        div_le_div_of_nonneg_right hg (by norm_num)
      have hc : (1 : ℝ) / 12 ≤ (3⁻¹ : ℝ) ^ 2 := by norm_num
      linarith
    have hsq : shiftDistance (nearBox d N) F g ^ 2 ≤ (3⁻¹ : ℝ) ^ 2 := by
      refine hb.trans ?_
      rw [hsum]
      exact hbound
    have hfin : shiftDistance (nearBox d N) F g ≤ 3⁻¹ := by
      have hnn : (0 : ℝ) ≤ shiftDistance (nearBox d N) F g :=
        shiftDistance_nonneg (nearBox d N) F g
      have := sq_le_sq.mp hsq
      rwa [abs_of_nonneg hnn, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3⁻¹)] at this
    rw [shiftDistanceTV_push (gridEmb d N) he (nearBox d N) F g,
      ← shiftDistance_eq_shiftDistanceTV (nearBox d N) F g]
    exact hfin

/-! ## Note d'adaptation (brique k4.3)

**Statut** : 17 briques closes — le `Komlos/NearInvariant.lean` de l'oracle est porté
**en intégralité**, et le Lemme 1.5 est désormais un théorème du lake. La campagne
k4 est complète : le poids produit (k4.2a), sa borne de distance (k4.2b), le
transport du décalage (k4.2c) et la distribution quasi-invariante (k4.3) forment une
chaîne close, `exists_nearInvariant` ne consommant **que** des briques closes.

**Ce qui a changé par rapport à l'oracle** :

1. **Le support est uniforme, pas canonique.** L'oracle laisse le support suivre le
   `Finsupp` ; le lake le rend existentiel, donc **indépendant du décalage** : c'est
   `nearBox d N` (`[-7N, 7N]^d`), qui majore `shiftBox N h` pour tout `h` admissible
   et sur laquelle la distance de décalage **est** celle de `shiftBox`
   (`shiftDistance_nearBox_eq_shiftBox`). Le prix de l'uniformité est un `+N` sur la
   boîte — visible dans l'énoncé du module, invisible dans ses conclusions.
2. **`IsDist` est rendu en clair** (positivité ponctuelle, masse 1) — le vocabulaire
   reste hors du lake depuis k1.1, comme k2.5 l'a arbitré pour `mean_mem_convexHull`.
3. **`sum_smul_eq_zero_of_neg` (lemme `Finsupp` générique de l'oracle) n'est pas
   porté tel quel** : sa substance — un poids pair sur une boîte symétrique a un
   moment coordonné nul — est prouvée directement par ré-indexation `Finset.sum_map`
   sur la négation (`nearBox_neg`, `cubeF_neg`), sans `equivMapDomain` ni
   `Finsupp.sum_neg`, qui n'ont pas d'objet ici.
4. **La moyenne se lit coordonnée par coordonnée** (`coordMomentReal`, k2.3) — la
   grille réelle n'a pas de `mean` vectoriel dans ce lake, elle a des moments.

**Ce que le lemme ne fait pas** : il ne calcule pas la distance de décalage, il la
**borne** — `≤ 3⁻¹` vient de la borne de k4.2 (`≤ (Σ k, ((g k)/N)²)/12 ≤ 1/12`) par
passage à la racine carrée ; et il ne choisit pas le point `g` : l'énoncé quantifie
sur **tout** `g` admissible, ce qui est exactement la force que l'assemblage
consommera.

**Vérification** : `lake build Discrepancy.Komlos.NearInvariant` (module + jumeau),
0 `sorry`, `distinct_code_sorry = 0` sur le lake. -/

end Discrepancy.Komlos
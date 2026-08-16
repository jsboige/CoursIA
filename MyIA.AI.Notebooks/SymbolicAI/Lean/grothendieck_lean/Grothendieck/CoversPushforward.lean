/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 45 : forme flèche de l'adjonction pushforward-pullback

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-44 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback,
les lois de treillis indexées et la forme flèche des topologies extrémales.

Cette partie applique le fil conducteur « forme flèche » à l'adjonction
pushforward-pullback des cribles. Mathlib fournit l'adjonction
`Sieve.galoisConnection (Sieve.pushforward f) (Sieve.pullback f)` avec ses
unit/counit (`Sieve.le_pushforward_pullback`, `Sieve.pullback_pushforward_le`),
sa monotonie et ses égalités (`Sieve.pushforward_comp`,
`Sieve.pushforward_union`), mais aucune loi de la forme flèche `J.Covers` n'y
est attachée. On fournit ici : la couverture du pushforward d'une couverture
(`covers_pushforward_of_mem`), la forme flèche de la monotonie, de la
composition et de l'union, le comportement sur l'identité, et les points
fixes de l'adjonction — pour `f` mono, `(S.pushforward f).pullback f = S`
(coinsertion) ; pour `f` split epi, `(R.pullback f).pushforward f = R`
(insertion) — prouvés par anti-symétrie, et leurs formes flèches.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversPushforward

open CategoryTheory

/-!
## Section 1 : l'unité de l'adjonction à la forme flèche

L'unité `Sieve.le_pushforward_pullback` dit `S ≤ (S.pushforward f).pullback f`.
Avec la propriété de topologie `superset_covering`, une appartenance
`S ∈ J Y` se transporte donc à la couverture `J.Covers (S.pushforward f) f` :
le pushforward d'une couverture le long de `f` recouvre `f` lui-même.
-/

/-- Le pushforward d'une couverture couvre la flèche le long de laquelle on
    pousse : `S ∈ J Y → J.Covers (S.pushforward f) f`.
    Preuve : `covers_iff` ramène à `(S.pushforward f).pullback f ∈ J Y`, puis
    `superset_covering` avec l'unité `Sieve.le_pushforward_pullback`. -/
theorem covers_pushforward_of_mem {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) (S : Sieve Y) (hS : S ∈ J Y) :
    J.Covers (S.pushforward f) f := by
  rw [GrothendieckTopology.covers_iff]
  exact J.superset_covering (Sieve.le_pushforward_pullback f S) hS

/-!
## Section 2 : monotonie, composition et union à la forme flèche

`Sieve.pushforward_monotone` et les égalités `Sieve.pushforward_comp` /
`Sieve.pushforward_union` se traduisent directement en lois de la forme
flèche : la couverture par un pushforward est monotone en le crible, et
invariante par les réécritures structurelles de la composition et de l'union.
-/

/-- La forme flèche est monotone en le crible : `A ≤ B` et `A.pushforward f`
    couvre `g` impliquent que `B.pushforward f` couvre `g`.
    Preuve : monotonie du pushforward (`Sieve.pushforward_monotone`), puis
    monotonie du pullback (`Sieve.pullback_monotone`) et `superset_covering`. -/
theorem covers_pushforward_monotone {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) {A B : Sieve Y} (hAB : A ≤ B) {Z : C} (g : Z ⟶ X)
    (h : J.Covers (A.pushforward f) g) :
    J.Covers (B.pushforward f) g := by
  rw [GrothendieckTopology.covers_iff] at h ⊢
  exact J.superset_covering (Sieve.pullback_monotone g (Sieve.pushforward_monotone f hAB)) h

/-- La forme flèche commute avec la composition des pushforwards :
    `J.Covers (S.pushforward (g ≫ f)) t ↔ J.Covers ((S.pushforward g).pushforward f) t`.
    Preuve : réécriture de l'égalité `Sieve.pushforward_comp`. -/
theorem covers_pushforward_comp {C : Type*} [Category C] {X Y Z : C} (J : GrothendieckTopology C)
    (S : Sieve Z) (f : Y ⟶ X) (g : Z ⟶ Y) {W : C} (t : W ⟶ X) :
    J.Covers (S.pushforward (g ≫ f)) t ↔ J.Covers ((S.pushforward g).pushforward f) t := by
  rw [Sieve.pushforward_comp]

/-- La forme flèche distribue sur l'union des cribles :
    `J.Covers ((S ⊔ R).pushforward f) t ↔ J.Covers (S.pushforward f ⊔ R.pushforward f) t`.
    Preuve : réécriture de l'égalité `Sieve.pushforward_union`. -/
theorem covers_pushforward_union {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) (S R : Sieve Y) {Z : C} (t : Z ⟶ X) :
    J.Covers ((S ⊔ R).pushforward f) t ↔ J.Covers (S.pushforward f ⊔ R.pushforward f) t := by
  rw [Sieve.pushforward_union]

/-!
## Section 3 : le pushforward le long de l'identité

Le pushforward le long de `𝟙 X` est l'identité sur les cribles. Mathlib ne
fournit pas cette identité ; on la prouve par extensionnalité (un crible
contient `f` si et seulement si `f ≫ 𝟙 X` y appartient). La forme flèche de
cette identité retombe alors sur l'appartenance ponctuelle.
-/

/-- Le pushforward le long de l'identité est l'identité : `S.pushforward (𝟙 X) = S`.
    Preuve : `Sieve.ext` — le membre gauche contient `f` ssi
    `∃ g, g ≫ 𝟙 X = f ∧ S g`, ce qui est équivalent à `S f`
    (`Category.comp_id`). -/
theorem pushforward_id {C : Type*} [Category C] {X : C} (S : Sieve X) :
    S.pushforward (𝟙 X) = S := by
  ext Y f
  constructor
  · rintro ⟨g, hg, hS⟩
    rwa [← hg, Category.comp_id]
  · intro hS
    exact ⟨f, by simp, hS⟩

/-- La forme flèche du pushforward de l'identité au-dessus de l'identité
    coïncide avec l'appartenance ponctuelle :
    `J.Covers (S.pushforward (𝟙 X)) (𝟙 X) ↔ S ∈ J X`.
    Preuve : `pushforward_id`, puis `covers_iff` et `Sieve.pullback_id`. -/
theorem covers_pushforward_id {C : Type*} [Category C] {X : C} (J : GrothendieckTopology C)
    (S : Sieve X) :
    J.Covers (S.pushforward (𝟙 X)) (𝟙 X) ↔ S ∈ J X := by
  rw [pushforward_id]
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_id]

/-!
## Section 4 : les points fixes de l'adjonction

Mathlib fournit les deux faces de l'adjonction : pour `f` mono,
`Sieve.galoisCoinsertionOfMono` (coreflective) ; pour `f` split epi,
`Sieve.galoisInsertionOfIsSplitEpi` (reflective). Les propriétés `u_l_le` et
`le_l_u` donnent chacune une inégalité ; combinées à l'unité/counit opposées,
l'anti-symétrie fournit les points fixes exacts, que Mathlib ne donne pas.
On les prouve ici, puis on en déduit leurs formes flèches.
-/

/-- Point fixe de la coinsertion : pour `f` mono, `(S.pushforward f).pullback f = S`.
    Preuve : anti-symétrie entre l'unité `Sieve.le_pushforward_pullback` et
    la propriété `u_l_le` de `Sieve.galoisCoinsertionOfMono`. -/
theorem pushforward_pullback_fixed {C : Type*} [Category C] {X Y : C} {f : Y ⟶ X} [Mono f]
    (S : Sieve Y) :
    (S.pushforward f).pullback f = S := by
  exact le_antisymm ((Sieve.galoisCoinsertionOfMono f).u_l_le S)
    (Sieve.le_pushforward_pullback f S)

/-- Forme flèche du point fixe de la coinsertion : pour `f` mono,
    `J.Covers (S.pushforward f) f ↔ J.Covers S (𝟙 Y)`.
    Preuve : `covers_iff` des deux côtés, `Sieve.pullback_id`, puis le point
    fixe `pushforward_pullback_fixed`. -/
theorem covers_pushforward_fixed_mono {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    {f : Y ⟶ X} [Mono f] (S : Sieve Y) :
    J.Covers (S.pushforward f) f ↔ J.Covers S (𝟙 Y) := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff, Sieve.pullback_id]
  rw [pushforward_pullback_fixed S]

/-- Point fixe de l'insertion : pour `f` split epi, `(R.pullback f).pushforward f = R`.
    Preuve : anti-symétrie entre la counit `Sieve.pullback_pushforward_le` et
    la propriété `le_l_u` de `Sieve.galoisInsertionOfIsSplitEpi`. -/
theorem pullback_pushforward_fixed {C : Type*} [Category C] {X Y : C} {f : Y ⟶ X} [IsSplitEpi f]
    (R : Sieve X) :
    (R.pullback f).pushforward f = R := by
  exact le_antisymm (Sieve.pullback_pushforward_le f R)
    ((Sieve.galoisInsertionOfIsSplitEpi f).le_l_u R)

end Grothendieck.CoversPushforward

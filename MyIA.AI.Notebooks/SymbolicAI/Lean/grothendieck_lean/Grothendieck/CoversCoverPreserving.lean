/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 50 : forme flèche des foncteurs qui préservent les couvertures

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-49 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback,
les lois de treillis indexées, la forme flèche des topologies dense,
extrémales, de l'adjonction pushforward-pullback, du bind, de la topologie
engendrée par une prétopologie et de la topologie induite le long d'un
foncteur.

Cette partie applique le fil conducteur « forme flèche » aux **foncteurs qui
préservent les couvertures**. Mathlib définit la structure `CoverPreserving
J K G` de façon **ponctuelle** (`cover_preserve : S ∈ J U → S.functorPushforward
G ∈ K (G.obj U)`) — structure au cœur de la théorie des sites
(`inducedTopology_coverPreserving`, morphismes de sites) — mais **aucune loi
ne connecte `CoverPreserving` à la forme flèche `J.Covers S f`**. On comble
le trou : le théorème central (`covers_pushforward_of_coverPreserving`,
transport d'une couverture le long de `f` par le foncteur), sa retombée
sur l'identité, et le pont vers la topologie induite
(`covers_inducedTopology`, corollaire de `inducedTopology_coverPreserving`).

Le lemme pivot est `Sieve.functorPushforward_pullback_le` : l'image par `G`
du pullback de `S` le long de `f` est contenue dans le pullback (le long de
`G.map f`) de l'image de `S`. C'est le diagramme de naturalité
pushforward/pullback, dont la stabilité par pullback de la topologie
(`J.pullback_stable`) couplée à la monotonie (`J.superset_covering`) donne
exactement le transport demandé.
-/

import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

namespace Grothendieck.CoversCoverPreserving

open CategoryTheory

/-!
## Section 1 : le théorème central

Un foncteur cover-preserving transporte la forme flèche de la couverture :
si `J` couvre `f` par `S`, alors `K` couvre `G.map f` par l'image
`S.functorPushforward G`. La preuve déplie `covers_iff` des deux côtés,
applique `G.cover_preserve` au pullback couvrant, puis relève le résultat
dans `K` par monotonie le long du diagramme de naturalité.
-/

universe u v u' v'

/-- Transport de la forme flèche par un foncteur cover-preserving :
    `J.Covers S f → K.Covers (S.functorPushforward G) (G.map f)`.
    Preuve : `covers_iff` réduit au ponctuel, `G.cover_preserve` transporte
    `S.pullback f ∈ J Y` vers `(S.pullback f).functorPushforward G ∈ K (G.obj Y)`,
    puis `K.superset_covering` avec `Sieve.functorPushforward_pullback_le`
    (le diagramme pushforward/pullback) relève dans `K`. -/
theorem covers_pushforward_of_coverPreserving {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} (hG : CoverPreserving J K G) {X Y : C} (f : Y ⟶ X) (S : Sieve X)
    (hS : J.Covers S f) : K.Covers (S.functorPushforward G) (G.map f) := by
  rw [GrothendieckTopology.covers_iff] at hS ⊢
  have hLe : (S.pullback f).functorPushforward G ≤ (S.functorPushforward G).pullback (G.map f) := by
    rw [Sieve.functorPushforward_le_iff_le_functorPullback]
    rw [Sieve.functorPullback_pullback]
    exact Sieve.pullback_monotone _ (Sieve.le_functorPushforward_pullback _ _)
  exact K.superset_covering hLe (hG.cover_preserve hS)

/-!
## Section 2 : retombée sur l'identité

`G.map (𝟙 X) = 𝟙 (G.obj X)` réduit le transport à la forme ponctuelle.
-/

/-- Retombée sur l'identité : la forme flèche transportée par `G` se réduit à
    la stabilité ponctuelle `S ∈ J X → S.functorPushforward G ∈ K (G.obj X)`
    une fois `G.map (𝟙 X)` simplifié.
    Preuve : application directe du théorème central à `f = 𝟙 X`, puis
    `Functor.map_id`. -/
theorem covers_id_of_coverPreserving {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} (hG : CoverPreserving J K G) {X : C} (S : Sieve X)
    (hS : J.Covers S (𝟙 X)) : K.Covers (S.functorPushforward G) (𝟙 (G.obj X)) := by
  simpa using covers_pushforward_of_coverPreserving hG (𝟙 X) S hS

/-!
## Section 3 : pont vers la topologie induite

`inducedTopology_coverPreserving` affirme que `G` est cover-preserving pour
`G.inducedTopology K` (la topologie induite le long de `G`, partie 49). Le
théorème central spécialisé donne alors la forme flèche du pont : une
couverture de la topologie induite est transportée par `G` en une
couverture de `K`. C'est la contrepartie flèche du fait que l'image d'un
crible induit-couvrant est couvrante dans `K`.
-/

/-- Pont vers la topologie induite : `(G.inducedTopology K).Covers S f`
    implique `K.Covers (S.functorPushforward G) (G.map f)`.
    Preuve : `Functor.inducedTopology_coverPreserving` fournit le foncteur
    cover-preserving, le théorème central conclut. -/
theorem covers_inducedTopology {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (G : C ⥤ D) (K : GrothendieckTopology D)
    [G.IsLocallyFull K] [G.IsLocallyFaithful K] [G.LocallyCoverDense K]
    {X Y : C} (f : Y ⟶ X) (S : Sieve X) (hS : (G.inducedTopology K).Covers S f) :
    K.Covers (S.functorPushforward G) (G.map f) :=
  covers_pushforward_of_coverPreserving
    (Functor.inducedTopology_coverPreserving (G := G) (K := K)) f S hS

end Grothendieck.CoversCoverPreserving

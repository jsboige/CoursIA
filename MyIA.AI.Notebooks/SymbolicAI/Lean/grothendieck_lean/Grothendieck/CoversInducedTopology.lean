/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 49 : forme flèche de la topologie induite

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-48 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback,
les lois de treillis indexées, la forme flèche des topologies dense,
extrémales, de l'adjonction pushforward-pullback, du bind et de la topologie
engendrée par une prétopologie.

Cette partie applique le fil conducteur « forme flèche » à la **topologie
induite** le long d'un foncteur. Quand `G : C ⥤ (D, K)` est localement dense
et localement plein/fidèle, Mathlib construit une topologie `G.inducedTopology
K` sur `C` (les cribles dont l'image par `G` est couvrante dans `D`) et prouve
`mem_inducedTopology_sieves_iff` — mais **aucune loi ne connecte cette
topologie à la forme flèche `J.Covers`**. On comble le trou : la forme flèche
caractéristique (`covers_iff`, par `functorPushforward` du pullback), le pont
vers les couvertures de `K` par existence d'un pullback (`covers_iff_exists`),
et les retombées (identité, appartenance ponctuelle, monotonie, stabilité par
précomposition).
-/

import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

namespace Grothendieck.CoversInducedTopology

open CategoryTheory

/-!
## Section 1 : la forme flèche de la topologie induite

La topologie induite déclare un crible `S` couvrant sur `X` dès que son image
`S.functorPushforward G` est couvrante dans `D` (`mem_inducedTopology_sieves_iff`).
En forme flèche, `G.inducedTopology K` couvre `f : Y ⟶ X` par `S` si et
seulement si l'image par `G` du pullback `S.pullback f` est couvrante dans
`K (G.obj Y)`. C'est exactement `covers_iff` de Mathlib, spécialisé à la
topologie induite.
-/

/-- Forme flèche de `mem_inducedTopology_sieves_iff` : `G.inducedTopology K`
    couvre `f : Y ⟶ X` par `S` si et seulement si l'image par `G` du pullback
    `S.pullback f` est couvrante dans `K (G.obj Y)`.
    Preuve : `covers_iff` réduit le membre gauche à
    `S.pullback f ∈ G.inducedTopology K Y`, puis
    `mem_inducedTopology_sieves_iff` identifie l'appartenance à la topologie
    induite avec l'appartenance de l'image par `G`. -/
theorem covers_iff {C : Type*} [Category C] {D : Type*} [Category D] (G : C ⥤ D)
    (K : GrothendieckTopology D) [G.LocallyCoverDense K] [G.IsLocallyFull K]
    [G.IsLocallyFaithful K] {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (G.inducedTopology K).Covers S f ↔
      (S.pullback f).functorPushforward G ∈ K (G.obj Y) := by
  rw [GrothendieckTopology.covers_iff, Functor.mem_inducedTopology_sieves_iff]

/-!
## Section 2 : le pont vers les couvertures de `K`

Sous l'hypothèse que `G` est plein et fidèle, le théorème de Mathlib
`pushforward_cover_iff_cover_pullback` caractérise l'appartenance de l'image
par un pullback : `R.functorPushforward G ∈ K (G.obj Y)` si et seulement si
il existe une couverture `T` de `K (G.obj Y)` dont le pullback par `G` est
exactement `R`. Combiné à `covers_iff`, cela donne la forme flèche complète
de la topologie induite : `S` couvre `f` si et seulement si `S.pullback f`
est le pullback (par `G`) d'une couverture de `K` sur `G.obj Y`.
-/

/-- La forme flèche de la topologie induite, via le pont de
    `pushforward_cover_iff_cover_pullback` : `G.inducedTopology K` couvre
    `f : Y ⟶ X` par `S` si et seulement s'il existe une couverture
    `T : K (G.obj Y)` dont le pullback par `G` est `S.pullback f`.
    Preuve : `covers_iff` ramène au membre de droite ; le théorème de Mathlib
    `pushforward_cover_iff_cover_pullback` (plein + fidèle) convertit
    l'appartenance de l'image en existence d'un tel `T`. -/
theorem covers_iff_exists {C : Type*} [Category C] {D : Type*} [Category D]
    (G : C ⥤ D) (K : GrothendieckTopology D) [G.LocallyCoverDense K]
    [G.IsLocallyFull K] [G.IsLocallyFaithful K] [G.Full] [G.Faithful]
    {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (G.inducedTopology K).Covers S f ↔
      ∃ T : K (G.obj Y), T.val.functorPullback G = S.pullback f := by
  rw [covers_iff, Functor.pushforward_cover_iff_cover_pullback]

/-!
## Section 3 : identité et appartenance ponctuelle

`Sieve.pullback_id` rend le pullback le long de l'identité trivial :
`S.pullback (𝟙 X) = S`. La forme flèche de `G.inducedTopology K` au-dessus de
`𝟙 X` retombe donc exactement sur l'appartenance ponctuelle
`S ∈ G.inducedTopology K X`.
-/

/-- La forme flèche de `G.inducedTopology K` au-dessus de l'identité coïncide
    avec l'appartenance ponctuelle : `S` couvre `𝟙 X` si et seulement si
    `S ∈ G.inducedTopology K X`.
    Preuve : `covers_iff` puis `Sieve.pullback_id`. -/
theorem covers_id {C : Type*} [Category C] {D : Type*} [Category D] (G : C ⥤ D)
    (K : GrothendieckTopology D) [G.LocallyCoverDense K] [G.IsLocallyFull K]
    [G.IsLocallyFaithful K] {X : C} (S : Sieve X) :
    (G.inducedTopology K).Covers S (𝟙 X) ↔ S ∈ G.inducedTopology K X := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_id]

/-- Le membre de droite de `covers_iff` au-dessus de l'identité, déplié :
    `S` couvre `𝟙 X` si et seulement si `S.functorPushforward G ∈ K (G.obj X)`.
    Preuve : `covers_id` puis `mem_inducedTopology_sieves_iff`. -/
theorem covers_id_iff {C : Type*} [Category C] {D : Type*} [Category D]
    (G : C ⥤ D) (K : GrothendieckTopology D) [G.LocallyCoverDense K]
    [G.IsLocallyFull K] [G.IsLocallyFaithful K] {X : C} (S : Sieve X) :
    (G.inducedTopology K).Covers S (𝟙 X) ↔ S.functorPushforward G ∈ K (G.obj X) := by
  rw [covers_id, Functor.mem_inducedTopology_sieves_iff]

/-!
## Section 4 : monotonie

`Sieve.functorPushforward` est monotone : si `S ≤ R`, alors
`S.functorPushforward G ≤ R.functorPushforward G`. La propriété de topologie
`superset_covering` de `K` transporte alors l'appartenance de l'image de `S`
à celle de l'image de `R`, et `covers_iff` donne la monotonie de la forme
flèche : si `S` couvre `f`, tout sur-crible `R` couvre aussi `f`.
-/

/-- La forme flèche de la topologie induite est monotone : si `S` couvre
    `f : Y ⟶ X`, alors tout sur-crible `R` de `S` couvre aussi `f`.
    Preuve : `covers_iff` des deux côtés, `Sieve.functorPushforward_monotone`
    transporte `S ≤ R` aux images, et `superset_covering` de `K` conclut. -/
theorem covers_monotone {C : Type*} [Category C] {D : Type*} [Category D]
    (G : C ⥤ D) (K : GrothendieckTopology D) [G.LocallyCoverDense K]
    [G.IsLocallyFull K] [G.IsLocallyFaithful K] {X Y : C} {S R : Sieve X}
    (hSR : S ≤ R) (f : Y ⟶ X) (hS : (G.inducedTopology K).Covers S f) :
    (G.inducedTopology K).Covers R f := by
  rw [covers_iff] at hS ⊢
  exact K.superset_covering
    ((Sieve.functorPushforward_monotone (F := G) (X := Y)) (Sieve.pullback_monotone f hSR)) hS

/-!
## Section 5 : stabilité par précomposition

La propriété de topologie `pullback_stable` de `G.inducedTopology K` dit
qu'une flèche dans la topologie induite se transporte le long d'un pullback.
Par l'identité `S.pullback (g ≫ f) = (S.pullback f).pullback g`
(`Sieve.pullback_comp`), c'est exactement la stabilité de la forme flèche :
si `S` couvre `f`, il couvre aussi `g ≫ f` pour toute `g : Z ⟶ Y`.
-/

/-- La forme flèche de `G.inducedTopology K` est stable par précomposition :
    si `S` couvre `f : Y ⟶ X`, alors `S` couvre aussi `g ≫ f` pour toute
    `g : Z ⟶ Y`.
    Preuve : `covers_iff` des deux côtés, puis `Sieve.pullback_comp`
    identifie `S.pullback (g ≫ f)` à `(S.pullback f).pullback g`, et
    `pullback_stable g` de la topologie induite conclut. -/
theorem covers_precomp {C : Type*} [Category C] {D : Type*} [Category D]
    (G : C ⥤ D) (K : GrothendieckTopology D) [G.LocallyCoverDense K]
    [G.IsLocallyFull K] [G.IsLocallyFaithful K] {X Y Z : C} (S : Sieve X)
    (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : (G.inducedTopology K).Covers S f) :
    (G.inducedTopology K).Covers S (g ≫ f) := by
  rw [covers_iff] at h ⊢
  rw [Sieve.pullback_comp]
  exact (G.inducedTopology K).pullback_stable g h

end Grothendieck.CoversInducedTopology

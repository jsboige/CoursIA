/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 47 : formes flèches des topologies extrémales

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-46 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback,
les lois de treillis indexées, la forme flèche des topologies denses et la
forme flèche de l'adjonction pushforward-pullback et du bind.

Cette partie applique le fil conducteur « forme flèche » aux deux topologies
extrémales du treillis complet des topologies — la topologie discrète `⊤`
(où tout crible couvre) et la topologie triviale `⊥` (où seul le crible
maximal couvre) — et au pont entre la forme flèche et le type bundled
`J.Cover`. Mathlib définit ces topologies
(`GrothendieckTopology.discrete`, `GrothendieckTopology.trivial`) et les
identifie au haut et au bas du treillis via l'instance `CompleteLattice`,
mais aucune loi ne donne leur forme flèche : `(⊤).Covers S f` est toujours
vrai, `(⊥).Covers S f` équivaut à `S.pullback f = ⊤`. On comble le trou avec
la monotonie de la forme flèche selon l'ordre des topologies
(`monotone_covers`), les deux formes extrémales et le passage aller-retour
entre la forme flèche et les couvertures bundled (`covers_of_cover`,
`cover_of_covers`, `covers_iff_cover`).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversExtremal

open CategoryTheory

/-!
## Section 1 : l'ordre des topologies en forme flèche

L'ordre sur les topologies est l'inclusion point par point des cribles
couvrants (`GrothendieckTopology.instLEGrothendieckTopology`). La forme
flèche est monotone en la topologie : si `J₁ ≤ J₂` et si `J₁` couvre `f`,
alors `J₂` couvre `f`. Cette loi, absente de Mathlib, relie l'ordre du
treillis des topologies à la relation de couverture.
-/

/-- La forme flèche est monotone en la topologie : si `J₁ ≤ J₂` et si `J₁`
    couvre `f`, alors `J₂` couvre `f`. Preuve : `covers_iff` ramène les deux
    membres à l'appartenance du pullback dans les cribles couvrants, puis
    l'inclusion point par point portée par l'ordre. -/
theorem monotone_covers {C : Type*} [Category C] {X Y : C} {J₁ J₂ : GrothendieckTopology C}
    (h : J₁ ≤ J₂) (S : Sieve X) (f : Y ⟶ X) (hC : J₁.Covers S f) : J₂.Covers S f := by
  rw [GrothendieckTopology.covers_iff] at hC ⊢
  exact (GrothendieckTopology.le_def.mp h) Y hC

/-!
## Section 2 : la topologie discrète `⊤`

Mathlib définit `GrothendieckTopology.discrete`, la topologie où tout crible
est couvrant, et l'instance `CompleteLattice` l'identifie au haut du treillis
définitionnellement (`CompleteLattice.copy`, `discrete = ⊤`). La forme flèche
est donc triviale : `(⊤).Covers S f` est toujours vrai. C'est la retombée de
la définition, mais sa formulation en forme flèche unifie le langage de la
couverture et rend la topologie extrémale lisible dans la même notation que
les autres.
-/

/-- La topologie discrète couvre tout : `(⊤).Covers S f ↔ True`.
    Preuve : `covers_iff` puis l'appartenance dans le haut du treillis, qui
    est la topologie discrète définitionnellement. -/
theorem discrete_covers_iff {C : Type*} [Category C] {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) : (⊤ : GrothendieckTopology C).Covers S f ↔ True := by
  change (GrothendieckTopology.discrete C).Covers S f ↔ True
  rw [GrothendieckTopology.covers_iff]
  simp

/-- La topologie discrète couvre toute flèche : `(⊤).Covers S f`.
    Preuve : l'équivalence `discrete_covers_iff`. -/
theorem discrete_covers {C : Type*} [Category C] {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) : (⊤ : GrothendieckTopology C).Covers S f := by
  exact discrete_covers_iff S f |>.mp trivial

/-!
## Section 3 : la topologie triviale `⊥`

Mathlib définit `GrothendieckTopology.trivial`, la topologie où seul le
crible maximal couvre, et l'identifie au bas du treillis
(`trivial_eq_bot`, `trivial_covering`). La forme flèche est donc :
`(⊥).Covers S f` équivaut à `S.pullback f = ⊤` — le pullback de `S` le long
de `f` est le crible maximal, autrement dit `S` couvre le codomaine `Y`
uniquement si son pullback est la couverture triviale. On en tire les
retombées sur l'identité (`S = ⊤`) et le crible bas (`⊥` ne couvre jamais).
-/

/-- La topologie triviale couvre `f` par `S` si et seulement si le pullback
    de `S` le long de `f` est le crible maximal :
    `(⊥).Covers S f ↔ S.pullback f = ⊤`.
    Preuve : `covers_iff`, puis le bas du treillis est la topologie triviale
    (`trivial_eq_bot`) dont les cribles couvrants sont les cribles maximaux
    (`trivial_covering`). -/
theorem trivial_covers_iff {C : Type*} [Category C] {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) : (⊥ : GrothendieckTopology C).Covers S f ↔ S.pullback f = ⊤ := by
  change (GrothendieckTopology.trivial C).Covers S f ↔ S.pullback f = ⊤
  rw [GrothendieckTopology.covers_iff]
  rw [GrothendieckTopology.trivial_covering]

/-- Dans la topologie triviale, le crible maximal couvre toute flèche :
    `S = ⊤ → (⊥).Covers S f`.
    Preuve : réécriture de `trivial_covers_iff` avec `hS`, puis
    `Sieve.pullback_top` (le pullback du crible maximal est le crible
    maximal). -/
theorem trivial_covers_of_top {C : Type*} [Category C] {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) (hS : S = ⊤) : (⊥ : GrothendieckTopology C).Covers S f := by
  rw [trivial_covers_iff S f, hS, Sieve.pullback_top]

/-- Dans la topologie triviale, un crible couvre l'identité si et seulement
    s'il est maximal : `(⊥).Covers S (𝟙 X) ↔ S = ⊤`.
    Preuve : `trivial_covers_iff` puis `Sieve.pullback_id`. -/
theorem trivial_covers_id_iff {C : Type*} [Category C] {X : C}
    (S : Sieve X) : (⊥ : GrothendieckTopology C).Covers S (𝟙 X) ↔ S = ⊤ := by
  rw [trivial_covers_iff S (𝟙 X), Sieve.pullback_id]

/-- Dans la topologie triviale, le crible bas ne couvre jamais :
    `¬ (⊥).Covers ⊥ f`.
    Preuve : `trivial_covers_iff` puis `Sieve.pullback_bot` ramènent à
    `⊥ ≠ ⊤` dans le treillis des cribles, démontré en appliquant les deux
    cribles à l'identité `𝟙 Y`. -/
theorem trivial_bot_not_covers {C : Type*} [Category C] {X Y : C}
    (f : Y ⟶ X) : ¬ (⊥ : GrothendieckTopology C).Covers (⊥ : Sieve X) f := by
  rw [trivial_covers_iff (⊥ : Sieve X) f, Sieve.pullback_bot]
  intro h
  have h0 : (⊥ : Sieve Y) (𝟙 Y) = (⊤ : Sieve Y) (𝟙 Y) :=
    congrArg (fun T : Sieve Y => T (𝟙 Y)) h
  simp at h0

/-- La monotonie relie les extrêmes : toute couverture de la topologie
    triviale est une couverture de la topologie discrète :
    `(⊥).Covers S f → (⊤).Covers S f`.
    Preuve : `monotone_covers` appliquée à `bot_le`. -/
theorem extremal_covers {C : Type*} [Category C] {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) (h : (⊥ : GrothendieckTopology C).Covers S f) :
    (⊤ : GrothendieckTopology C).Covers S f := by
  exact
    monotone_covers (bot_le : (⊥ : GrothendieckTopology C) ≤ (⊤ : GrothendieckTopology C)) S f h

/-!
## Section 4 : le pont entre la forme flèche et les couvertures bundled

Le type `J.Cover X` de Mathlib est le sous-type des cribles couvrants de
`X` — la couverture « bundled ». La forme flèche et cette présentation sont
les deux faces d'un même objet : une couverture bundled couvre toute flèche
vers son objet (`covers_of_cover`, instanciation de la forme flèche de
`pullback_stable`), et réciproquement une couverture en forme flèche
`J.Covers S f` engendre la couverture bundled `S.pullback f`
(`cover_of_covers`). Le pont bidirectionnel `covers_iff_cover` clôt la
section : la forme flèche équivaut à l'existence de la couverture bundled
sous-jacente.
-/

/-- Une couverture bundled couvre toute flèche vers son objet :
    `(S : J.Cover X)` implique `J.Covers (S : Sieve X) f`.
    Preuve : forme flèche de `pullback_stable` — `S.condition` est
    l'appartenance du crible sous-jacent à la topologie, et `pullback_stable`
    fournit l'appartenance du pullback. -/
theorem covers_of_cover {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    {S : J.Cover X} (f : Y ⟶ X) : J.Covers (S : Sieve X) f := by
  rw [GrothendieckTopology.covers_iff]
  exact J.pullback_stable f S.condition

/-- La forme flèche engendre une couverture bundled : si `J.Covers S f`,
    alors `S.pullback f` est une couverture de `Y`.
    Preuve : construction par le sous-type, l'hypothèse étant exactement
    l'appartenance du pullback à la topologie (`covers_iff`). -/
def cover_of_covers {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S : Sieve X) (f : Y ⟶ X) (h : J.Covers S f) : J.Cover Y :=
  ⟨S.pullback f, h⟩

/-- Le crible sous-jacent de `cover_of_covers` est le pullback de `S`.
    Preuve : `rfl` (la construction définit exactement ce crible). -/
theorem cover_of_covers_coe {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S : Sieve X) (f : Y ⟶ X) (h : J.Covers S f) :
    (cover_of_covers J S f h : Sieve Y) = S.pullback f := rfl

/-- La forme flèche équivaut à l'existence de la couverture bundled
    sous-jacente : `J.Covers S f ↔ ∃ T : J.Cover Y, (T : Sieve Y) = S.pullback f`.
    Preuve : direction directe par `cover_of_covers`, réciproque par la
    condition de la couverture bundled (la preuve de `T` est l'appartenance
    du pullback à la topologie). -/
theorem covers_iff_cover {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S : Sieve X) (f : Y ⟶ X) :
    J.Covers S f ↔ ∃ T : J.Cover Y, (T : Sieve Y) = S.pullback f := by
  constructor
  · intro h
    exact ⟨cover_of_covers J S f h, rfl⟩
  · rintro ⟨T, hT⟩
    rw [GrothendieckTopology.covers_iff, ← hT]
    exact T.condition

end Grothendieck.CoversExtremal

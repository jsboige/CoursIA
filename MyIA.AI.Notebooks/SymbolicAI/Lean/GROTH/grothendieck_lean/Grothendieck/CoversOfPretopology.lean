/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 48 : formes flèches de la topologie engendrée par une prétopologie

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-47 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback,
les lois de treillis indexées, la forme flèche des topologies denses, la
forme flèche de l'adjonction pushforward-pullback, du bind et des topologies
extrémales.

Cette partie applique le fil conducteur « forme flèche » à la topologie
engendrée par une prétopologie. Mathlib définit la complétion
`Pretopology.toGrothendieck` (un crible est couvrant s'il contient une
famille de la prétopologie) et l'adjonction de Galois `Pretopology.gi`, mais
aucune loi ne donne sa forme flèche : la relation `(K.toGrothendieck).Covers
S f` n'est jamais connectée à la prétopologie `K`. On comble le trou avec la
forme flèche caractéristique (`covers_iff_of_pretopology`), ses retombées sur
l'identité et le crible maximal, la présentation par `Sieve.generate`, la
monotonie de la topologie engendrée et les lois de l'adjonction de Galois.
-/

import Mathlib.CategoryTheory.Sites.Pretopology

namespace Grothendieck.CoversOfPretopology

open CategoryTheory

/-!
## Section 1 : la forme flèche de la topologie engendrée

La complétion `Pretopology.toGrothendieck` déclare un crible `S` couvrant sur
`X` dès qu'il contient une famille `R` de la prétopologie
(`Pretopology.mem_toGrothendieck`). En forme flèche, cela devient :
`K.toGrothendieck` couvre `f : Y ⟶ X` par `S` si et seulement si le pullback
`S.pullback f` contient une famille `R ∈ K Y`. Cette loi, absente de Mathlib,
est le cœur du pont entre une prétopologie et la topologie qu'elle engendre.
-/

/-- La forme flèche de la topologie engendrée par une prétopologie :
    `K.toGrothendieck` couvre `f : Y ⟶ X` par `S` si et seulement si le
    pullback `S.pullback f` contient une famille `R` de la prétopologie en
    `Y` : `∃ R ∈ K Y, R ≤ (S.pullback f : Presieve Y)`.
    Preuve : `covers_iff` ramène la couverture à l'appartenance du pullback,
    qui est exactement la définition de `toGrothendieck`
    (`Pretopology.mem_toGrothendieck`). -/
theorem covers_iff_of_pretopology {C : Type*} [Category C] [Limits.HasPullbacks C] {X Y : C} (K : Pretopology C)
    (S : Sieve X) (f : Y ⟶ X) :
    (K.toGrothendieck).Covers S f ↔ ∃ R ∈ K Y, R ≤ (S.pullback f : Presieve Y) := by
  rw [GrothendieckTopology.covers_iff]
  exact Pretopology.mem_toGrothendieck K Y (S.pullback f)

/-- La forme flèche directe : une famille `R ∈ K Y` contenue dans
    `S.pullback f` rend `K.toGrothendieck` couvrant.
    Preuve : l'implication directe de `covers_iff_of_pretopology`. -/
theorem covers_of_mem_pretopology {C : Type*} [Category C] [Limits.HasPullbacks C] {X Y : C} (K : Pretopology C)
    (S : Sieve X) (f : Y ⟶ X) {R : Presieve Y} (hR : R ∈ K Y)
    (hRS : R ≤ (S.pullback f : Presieve Y)) : (K.toGrothendieck).Covers S f := by
  exact (covers_iff_of_pretopology K S f).mpr ⟨R, hR, hRS⟩

/-- Le cas particulier où la famille témoin est le pullback lui-même : si
    `S.pullback f` est une famille de `K` en `Y`, alors `K.toGrothendieck`
    couvre.
    Preuve : `covers_of_mem_pretopology` avec le témoin `S.pullback f` et la
    réflexivité de l'ordre. -/
theorem covers_self_of_mem_pretopology {C : Type*} [Category C] [Limits.HasPullbacks C] {X Y : C} (K : Pretopology C)
    (S : Sieve X) (f : Y ⟶ X) (h : (S.pullback f : Presieve Y) ∈ K Y) :
    (K.toGrothendieck).Covers S f := by
  exact
    covers_of_mem_pretopology K S f h
      (le_rfl : (S.pullback f : Presieve Y) ≤ (S.pullback f : Presieve Y))

/-!
## Section 2 : retombées sur l'identité et le crible maximal

Deux retombées immédiates de la forme flèche. Sur l'identité, le pullback est
le crible lui-même (`Sieve.pullback_id`) : un crible de la prétopologie
couvre donc l'identité. Le crible maximal `⊤` est toujours couvrant le long
de toute flèche, car la prétopologie contient toujours un témoin — le
singleton de l'identité, par `Pretopology.has_isos` — et `⊤` est la famille
totale.
-/

/-- Un crible de la prétopologie couvre l'identité : `(S : Presieve X) ∈ K X`
    implique que `K.toGrothendieck` couvre `S (𝟙 X)`.
    Preuve : `covers_iff_of_pretopology`, puis le pullback le long de
    l'identité est le crible lui-même (`Sieve.pullback_id`) ; le témoin est
    `S` et l'ordre est réflexif. -/
theorem covers_id_of_mem_pretopology {C : Type*} [Category C] [Limits.HasPullbacks C] {X : C} (K : Pretopology C)
    (S : Sieve X) (h : (S : Presieve X) ∈ K X) : (K.toGrothendieck).Covers S (𝟙 X) := by
  rw [covers_iff_of_pretopology, Sieve.pullback_id]
  exact ⟨(S : Presieve X), h, (le_rfl : (S : Presieve X) ≤ (S : Presieve X))⟩

/-- La topologie engendrée couvre le crible maximal sur l'identité :
    `(K.toGrothendieck).Covers ⊤ (𝟙 X)`.
    Preuve : `covers_iff` puis le crible maximal appartient à toute topologie
    (`GrothendieckTopology.top_mem`), avec `Sieve.pullback_top`. -/
theorem covers_top_id {C : Type*} [Category C] [Limits.HasPullbacks C] {X : C} (K : Pretopology C) :
    (K.toGrothendieck).Covers (⊤ : Sieve X) (𝟙 X) := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_top]
  exact K.toGrothendieck.top_mem X

/-- La topologie engendrée couvre le crible maximal le long de toute flèche :
    `(K.toGrothendieck).Covers ⊤ f`.
    Preuve : la forme flèche ramène à une famille témoin ; la prétopologie
    contient toujours le singleton de l'identité (`Pretopology.has_isos`),
    et le singleton est contenu dans `⊤`, la famille totale. -/
theorem covers_top_of_pretopology {C : Type*} [Category C] [Limits.HasPullbacks C] {X Y : C} (K : Pretopology C)
    (f : Y ⟶ X) : (K.toGrothendieck).Covers (⊤ : Sieve X) f := by
  rw [covers_iff_of_pretopology, Sieve.pullback_top]
  refine ⟨Presieve.singleton (𝟙 Y), K.has_isos (𝟙 Y), ?_⟩
  intro Z g hg
  trivial

/-!
## Section 3 : la présentation par `Sieve.generate`

Un crible est une famille de flèches close par précomposition ; une
prétopologie s'exprime naturellement sur les familles (`Presieve`). Le
générateur `Sieve.generate` relie les deux via l'adjonction
`Sieve.generate ⊣ Presieve.arrows` (`Sieve.generate_le_iff`,
`Sieve.le_generate`). La forme flèche se réécrit donc aussi : `K.toGrothendieck`
couvre si et seulement si le pullback contient le générateur d'une famille de
la prétopologie.
-/

/-- La présentation par `generate` de la forme flèche : `K.toGrothendieck`
    couvre `S f` si et seulement s'il existe `R ∈ K Y` dont le générateur est
    contenu dans `S.pullback f` : `Sieve.generate R ≤ S.pullback f`.
    Preuve : `covers_iff_of_pretopology` puis l'adjonction
    `Sieve.generate ⊣ Presieve.arrows` (`Sieve.generate_le_iff`). -/
theorem covers_iff_generate_of_pretopology {C : Type*} [Category C] [Limits.HasPullbacks C] {X Y : C}
    (K : Pretopology C) (S : Sieve X) (f : Y ⟶ X) :
    (K.toGrothendieck).Covers S f ↔ ∃ R ∈ K Y, Sieve.generate R ≤ S.pullback f := by
  rw [covers_iff_of_pretopology]
  constructor
  · rintro ⟨R, hR, hRS⟩
    exact ⟨R, hR, (Sieve.generate_le_iff R (S.pullback f)).mpr hRS⟩
  · rintro ⟨R, hR, hgen⟩
    exact ⟨R, hR, (Sieve.generate_le_iff R (S.pullback f)).mp hgen⟩

/-- Une famille de la prétopologie couvre le générateur de son crible :
    `R ∈ K X` implique que `K.toGrothendieck` couvre `Sieve.generate R` le
    long de l'identité.
    Preuve : `covers_iff_of_pretopology`, le pullback le long de l'identité
    est le crible lui-même, et le témoin `R` est contenu dans son générateur
    (`Sieve.le_generate`). -/
theorem covers_generate_id_of_mem_pretopology {C : Type*} [Category C] [Limits.HasPullbacks C] {X : C}
    (K : Pretopology C) {R : Presieve X} (hR : R ∈ K X) :
    (K.toGrothendieck).Covers (Sieve.generate R) (𝟙 X) := by
  rw [covers_iff_of_pretopology, Sieve.pullback_id]
  exact ⟨R, hR, Sieve.le_generate R⟩

/-!
## Section 4 : monotonie et adjonction de Galois

La complétion `toGrothendieck` est monotone en la prétopologie, donc la forme
flèche aussi (`monotone_covers_of_le_pretopology`). L'adjonction de Galois
`Pretopology.gi` rend ces lois structurelles : la topologie engendrée est plus
petite qu'une topologie `J` si et seulement si la prétopologie est contenue
dans la prétopologie canonique de `J` (`toGrothendieck_le_iff`), et toute
prétopologie est contenue dans la prétopologie engendrée par sa complétion
(`le_toGrothendieck_toPretopology`), dont on donne la version ponctuelle
(`mem_toPretopology_of_mem`).
-/

/-- La forme flèche est monotone en la prétopologie : si `K₁ ≤ K₂` et si
    `K₁.toGrothendieck` couvre `S f`, alors `K₂.toGrothendieck` couvre aussi.
    Preuve : les deux formes flèches se ramènent à l'existence d'une famille
    témoin ; `Pretopology.le_def` propage l'appartenance de `K₁` à `K₂`. -/
theorem monotone_covers_of_le_pretopology {C : Type*} [Category C] [Limits.HasPullbacks C] {X Y : C}
    {K₁ K₂ : Pretopology C} (h : K₁ ≤ K₂) (S : Sieve X) (f : Y ⟶ X)
    (hC : (K₁.toGrothendieck).Covers S f) : (K₂.toGrothendieck).Covers S f := by
  rw [covers_iff_of_pretopology] at hC ⊢
  rcases hC with ⟨R, hR, hRS⟩
  exact ⟨R, (Pretopology.le_def.mp h) Y hR, hRS⟩

/-- Le caractère universel de la complétion : `K.toGrothendieck ≤ J` si et
    seulement si `K ≤ J.toPretopology` — la prétopologie canonique de `J`.
    Preuve : la Galois connection de `Pretopology.gi`. -/
theorem toGrothendieck_le_iff {C : Type*} [Category C] [Limits.HasPullbacks C] (K : Pretopology C)
    (J : GrothendieckTopology C) : K.toGrothendieck ≤ J ↔ K ≤ J.toPretopology := by
  exact (Pretopology.gi C).gc K J

/-- Toute prétopologie est contenue dans la prétopologie engendrée par sa
    complétion : `K ≤ K.toGrothendieck.toPretopology`.
    Preuve : la Galois connection de `Pretopology.gi` appliquée à
    `le_rfl` — `K.toGrothendieck ≤ K.toGrothendieck` équivaut, par le
    caractère universel, à `K ≤ K.toGrothendieck.toPretopology`. -/
theorem le_toGrothendieck_toPretopology {C : Type*} [Category C] [Limits.HasPullbacks C] (K : Pretopology C) :
    K ≤ K.toGrothendieck.toPretopology := by
  exact ((Pretopology.gi C).gc K (K.toGrothendieck)).mp le_rfl

/-- La version ponctuelle de l'unité : une famille `R ∈ K X` engendre un
    crible couvrant pour la topologie engendrée :
    `Sieve.generate R ∈ K.toGrothendieck X`.
    Preuve : `Pretopology.mem_toGrothendieck` ramène l'appartenance à
    l'existence d'un témoin de la prétopologie dans le générateur ; le témoin
    est `R` lui-même, contenu dans son générateur (`Sieve.le_generate`). -/
theorem mem_toPretopology_of_mem {C : Type*} [Category C] [Limits.HasPullbacks C] {X : C} (K : Pretopology C)
    {R : Presieve X} (hR : R ∈ K X) : Sieve.generate R ∈ K.toGrothendieck X := by
  rw [Pretopology.mem_toGrothendieck]
  exact ⟨R, hR, Sieve.le_generate R⟩

end Grothendieck.CoversOfPretopology

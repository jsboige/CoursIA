/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 35 : la forme fleche de la couverture

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-29 ont etabli les fondamentaux : categories, cribles, topologies,
lois de treillis, identites de pullback, bases de faisceaux, cloture couvrante,
calibration, sous-canonicalite, topologies denses, faisceaux, hom interne,
cohomologie de Cech, limite de Mayer-Vietoris, extensions de Kan, adjonctions,
monades, equivalences, categories monoidales, limites et colimites, couples
comma, images directes.

Ce module enregistre des **theoremes propres** sur la **forme fleche de la
couverture** : pour une topologie de Grothendieck `J` sur une categorie `C`, un
crible `S` sur `X` et un morphisme `f : Y ⟶ X`, la notation `J.Covers S f`
signifie que le pullback `S.pullback f` appartient a la famille `J Y`
(`GrothendieckTopology.Covers`). C'est la lecture « fleche apres fleche » de
l'axiome de stabilite par pullback : un crible est couvrant pour un morphisme
quand « le pullback le long de ce morphisme est couvrant ».

Les theoremes enonces ici sont des **preuves tactiques reelles** (veine DEEP,
a la difference des ponts re-export des parties precedentes) :

  - `covers_iff_covers_id` : couvrir le long de `f` equivaut a couvrir le
    pullback de `S` le long de l'identite (la couverture se reduit au but).
  - `covers_monotone` : la couverture est monotone dans le crible.
  - `covers_inf` : couvrir l'intersection de deux cribles equivaut a couvrir
    chacun d'eux (la topologie est un filtre).
  - `covers_union` : couvrir chacun de deux cribles implique couvrir leur
    reunion — implication unilaterale seulement : la topologie n'etant pas
    descendante, la reciproque est fausse en general.
  - `covers_comp_iff` : couvrir le pullback de `S` le long de `g` equivaut a
    couvrir `S` le long de `g ≫ f` (contravariance en la fleche, par
    `Sieve.pullback_comp`).
  - `inf_mem` : un crible appartient a `J₁ ⊓ J₂` ssi il appartient a `J₁` et
    a `J₂` (l'infimum de deux topologies est l'intersection des familles).
  - `inf_covers` : la forme fleche se comporte de meme pour l'infimum.

Chaque preuve mobilise un lemme Mathlib distinct (`Sieve.pullback_comp`,
`Sieve.pullback_monotone`, `GrothendieckTopology.arrow_intersect`,
`GrothendieckTopology.superset_covering`, `sInf_pair`, `mem_sInf`) — aucune
preuve n'est un simple re-export.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s elimines a la creation.

### Convention i18n (EPIC #4980 ratifiee par user 2026-07-04)

Ce module est apparie avec son jumeau anglais dans le fichier sibling
`CoversArrow_en.lean` (modele sibling pair, voir PR #6154 pour le pilote sur
`Utility.lean`). Namespace suffix `_en` applique au fichier EN (anti-collision,
conforme code-style.md #4980). Les enonces de theoremes, les noms de lemmes,
les tactiques Lean et les references Mathlib restent en anglais ; seules les
docstrings `/-- ... -/` et les commentaires `-- ...` different entre les deux
fichiers (preservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversArrow

open CategoryTheory

/-!
## Section 1 : premieres equivalences de la forme fleche

Rappel : `GrothendieckTopology.Covers S f` est definitionnellement
`S.pullback f ∈ J Y`, et `covers_iff` en est le lemme de reecriture
`J.Covers S f ↔ S.pullback f ∈ J Y`. Le premier theoreme reduit la
couverture le long d'une fleche a une couverture le long de l'identite ;
le second exprime la monotonie dans le crible.
-/

/-- Couvrir le long de `f` equivaut a couvrir le pullback de `S` le long de
    l'identite : `J.Covers S f ↔ J.Covers (S.pullback f) (𝟙 Y)`.
    Preuve : on developpe les deux formes fleches avec `covers_iff`, puis on
    reecrit `(S.pullback f).pullback (𝟙 Y)` en `S.pullback (𝟙 Y ≫ f)` par
    `Sieve.pullback_comp` (orientation inverse) et `𝟙 Y ≫ f` en `f` par
    `Category.id_comp`. Les deux membres deviennent definitionnellement
    egaux et `rw` conclut par reflexivite. -/
theorem covers_iff_covers_id {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S : Sieve X) (f : Y ⟶ X) :
    J.Covers S f ↔ J.Covers (S.pullback f) (𝟙 Y) := by
  rw [J.covers_iff S f, J.covers_iff (S.pullback f) (𝟙 Y),
    ← Sieve.pullback_comp, Category.id_comp]

/-- La couverture est monotone dans le crible : si `S ≤ R` et `S` couvre `f`,
    alors `R` couvre `f`.
    Preuve : on developpe les deux formes fleches avec `covers_iff`, puis le
    pullback est monotone (`Sieve.pullback_monotone f h : S.pullback f ≤
    R.pullback f`) et la topologie est close par sur-ensemble
    (`GrothendieckTopology.superset_covering`). -/
theorem covers_monotone {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) {S R : Sieve X} (f : Y ⟶ X)
    (h : S ≤ R) (hS : J.Covers S f) :
    J.Covers R f := by
  rw [J.covers_iff S f] at hS
  rw [J.covers_iff R f]
  exact J.superset_covering (Sieve.pullback_monotone f h) hS

/-!
## Section 2 : intersections, reunions et composition

Les deux theoremes suivants exploitent la structure de treillis des cribles.
`covers_inf` est une equivalence (la topologie est un filtre : la famille
couvrante est close par intersection finie, `arrow_intersect`). `covers_union`
n'est qu'une implication : la topologie n'est pas descendante, la reciproque
serait fausse en general.
-/

/-- Couvrir l'intersection de deux cribles equivaut a couvrir chacun d'eux :
    `J.Covers (S ⊓ R) f ↔ J.Covers S f ∧ J.Covers R f`.
    Preuve : le sens direct applique `covers_monotone` avec `inf_le_left` et
    `inf_le_right` ; le sens reciproque est exactement l'axiome d'intersection
    de la topologie, `GrothendieckTopology.arrow_intersect`. -/
theorem covers_inf {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S R : Sieve X) (f : Y ⟶ X) :
    J.Covers (S ⊓ R) f ↔ J.Covers S f ∧ J.Covers R f := by
  constructor
  · intro h
    exact ⟨covers_monotone J f inf_le_left h, covers_monotone J f inf_le_right h⟩
  · intro h
    exact J.arrow_intersect f S R h.1 h.2

/-- Couvrir chacun de deux cribles implique couvrir leur reunion :
    `J.Covers S f → J.Covers R f → J.Covers (S ⊔ R) f`.
    Preuve : `S ≤ S ⊔ R` (`le_sup_left`), donc le pullback de `S` est
    inferieur au pullback de `S ⊔ R` (`Sieve.pullback_monotone`), et la
    topologie est close par sur-ensemble (`superset_covering`).
    L'implication est unilaterale : la famille couvrante n'ayant pas de
    cloture descendante, `J.Covers (S ⊔ R) f` n'implique pas `J.Covers S f`
    en general. -/
theorem covers_union {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S R : Sieve X) (f : Y ⟶ X)
    (hS : J.Covers S f) (_hR : J.Covers R f) :
    J.Covers (S ⊔ R) f := by
  rw [J.covers_iff S f] at hS
  rw [J.covers_iff (S ⊔ R) f]
  exact J.superset_covering (Sieve.pullback_monotone f le_sup_left) hS

/-- Couvrir le pullback de `S` le long de `g` equivaut a couvrir `S` le long
    de `g ≫ f` : `J.Covers (S.pullback f) g ↔ J.Covers S (g ≫ f)`.
    Preuve : on developpe les deux formes fleches avec `covers_iff`, puis
    `Sieve.pullback_comp` (orientation inverse) identifie `(S.pullback f)
    .pullback g` et `S.pullback (g ≫ f)`. La forme fleche est contravariante
    en la fleche. -/
theorem covers_comp_iff {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (S : Sieve X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    J.Covers (S.pullback f) g ↔ J.Covers S (g ≫ f) := by
  rw [J.covers_iff (S.pullback f) g, J.covers_iff S (g ≫ f),
    ← Sieve.pullback_comp]

/-!
## Section 3 : l'infimum de deux topologies

Les deux derniers theoremes portent sur la structure d'ordre des topologies
elles-memes. `sInf_pair` (generateur dual `to_dual` de `sSup_pair`) identifie
`J₁ ⊓ J₂` a `sInf {J₁, J₂}`, et `GrothendieckTopology.mem_sInf` exprime
l'appartenance a une intersection de familles.
-/

/-- Un crible appartient a `J₁ ⊓ J₂` ssi il appartient a `J₁` et a `J₂` :
    `S ∈ (J₁ ⊓ J₂) X ↔ S ∈ J₁ X ∧ S ∈ J₂ X`.
    Preuve : `sInf_pair` ramene `J₁ ⊓ J₂` a `sInf {J₁, J₂}`, puis
    `GrothendieckTopology.mem_sInf` reformule l'appartenance en quantification
    universelle sur la paire. Le sens direct instancie chaque element de la
    paire (appartenance prouvee par `simp`) ; le sens reciproque fait une
    disjonction de cas sur `t = J₁ ∨ t = J₂` (`Set.mem_insert_iff` +
    `Set.mem_singleton_iff`). -/
theorem inf_mem {C : Type*} [Category C] {X : C} (J₁ J₂ : GrothendieckTopology C)
    (S : Sieve X) :
    S ∈ (J₁ ⊓ J₂) X ↔ S ∈ J₁ X ∧ S ∈ J₂ X := by
  rw [← sInf_pair]
  rw [GrothendieckTopology.mem_sInf ({J₁, J₂} : Set (GrothendieckTopology C)) S]
  constructor
  · intro h
    exact ⟨h J₁ (by simp), h J₂ (by simp)⟩
  · rintro ⟨h₁, h₂⟩ t ht
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact h₁
    · exact h₂

/-- La forme fleche se comporte de meme pour l'infimum :
    `(J₁ ⊓ J₂).Covers S f ↔ J₁.Covers S f ∧ J₂.Covers S f`.
    Preuve : on developpe les trois formes fleches avec `covers_iff` (le
    pullback de `S` le long de `f` est commun aux trois membres), puis on
    applique `inf_mem` au crible `S.pullback f`. -/
theorem inf_covers {C : Type*} [Category C] {X Y : C}
    (J₁ J₂ : GrothendieckTopology C) (S : Sieve X) (f : Y ⟶ X) :
    (J₁ ⊓ J₂).Covers S f ↔ J₁.Covers S f ∧ J₂.Covers S f := by
  rw [(J₁ ⊓ J₂).covers_iff S f, J₁.covers_iff S f, J₂.covers_iff S f]
  exact inf_mem J₁ J₂ (S.pullback f)

end Grothendieck.CoversArrow

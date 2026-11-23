/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 40 : lois de la forme flèche sous pullback

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-39 ont etabli les fondamentaux : categories, cribles,
topologies, lois de treillis, identites de pullback, bases de faisceaux,
cloture couvrante, calibration, sous-canonicalite, topologies denses,
faisceaux, hom interne, cohomologie de Cech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, equivalences, categories monoidales,
limites et colimites, couples comma, images directes, theoremes propres sur la
forme fleche (`J.Covers S f`), sur la couverture bundlee (`J.Cover X`), les
lois de coherence du pseudo-foncteur pullback (Partie 37), les lois de
foncteur du pullback (Partie 38) et les lois de treillis des topologies
(Partie 39).

La Partie 40 etablit les **lois de la forme fleche `J.Covers S f` sous
pullback** : Mathlib fournit les axiomes de topologie en forme fleche
(`arrow_max`, `arrow_stable`, `arrow_trans`, `arrow_intersect`) et le
definitif `covers_iff`, mais **ne fournit pas** les lois de comportement de
`J.Covers` vis-a-vis des operations sur les cribles et des morphismes. Ce
module les enonce et les prouve :

  - `covers_mono` : la forme fleche est monotone en le crible —
    si `A ≤ B` et `A` couvre `f`, alors `B` couvre `f`.
  - `covers_union` : la forme fleche est stable par borne superieure —
    si `S` couvre `f`, alors `S ⊔ R` couvre `f`.
  - `covers_pullback_comp` : **loi de changement de base** — couvrir la
    composee `g ≫ f` est equivalent a couvrir le pullback `S.pullback f` le
    long de `g`.
  - `covers_iso_cancel` : couvrir `g ≫ f` avec `g` iso est equivalent a
    couvrir `f` (cancellation par isomorphisme).
  - `covers_iso_covering` : une fleche isomorphe `e.hom` est couverte par `S`
    si et seulement si `S` est couvrant.
  - `covers_bind` : **caractere local en forme fleche** — si `S` couvre `f`
    et, pour chaque fleche `g` de `S`, le crible `R g` est couvrant sur son
    domaine, alors le crible lie `Sieve.bind S R` couvre `f`.
  - `covers_iff_exists_cover` : pont vers la couverture bundlee — `S` couvre
    `f` si et seulement si `S.pullback f` contient un `J.Cover Y`.
  - `cover_pullback_covers` : le pullback d'une couverture `S.pullback f`
    couvre l'identite de `Y` — la version `J.Covers` de
    `J.Cover.pullback` (Partie 38).

Chaque preuve est une **preuve tactique reelle** (veine DEEP) : les axiomes
de topologie (`superset_covering`, `pullback_mem_iff_of_isIso`,
`arrow_trans`) plus les lois de `Sieve.pullback` (`pullback_comp`,
`pullback_id`, `pullback_monotone`) et la loi d'adjonction du lie
(`Sieve.le_pullback_bind`). Aucune preuve n'est un re-export.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s elimines a la creation.

### Convention i18n (EPIC #4980 ratifiee par user 2026-07-04)

Ce module est apparie avec son jumeau anglais dans le fichier sibling
`CoversPullback_en.lean` (modele sibling pair, voir PR #6154 pour le pilote
sur `Utility.lean`). Namespace suffix `_en` applique au fichier EN
(anti-collision, conforme code-style.md #4980). Les enonces de theoremes, les
noms de lemmes, les tactiques Lean et les references Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
different entre les deux fichiers (preservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversPullback

open CategoryTheory

/-!
## Section 1 : monotonie et union

La forme fleche `J.Covers S f` est definie par `S.pullback f ∈ J Y`
(Mathlib, `covers_iff`). La monotonie en le crible suit de la monotonie du
pullback de cribles (`Sieve.pullback_monotone`) et de l'axiome
`superset_covering`. L'union est un cas particulier.
-/

/-- La forme fleche est monotone en le crible : si `A ≤ B` et `A` couvre `f`,
    alors `B` couvre `f`.
    Preuve : on ramene les deux membres a des appartenances (`covers_iff`),
    puis `superset_covering` avec la monotonie du pullback
    (`Sieve.pullback_monotone`). -/
theorem covers_mono {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) {A B : Sieve X} (hAB : A ≤ B) (h : J.Covers A f) :
    J.Covers B f := by
  rw [GrothendieckTopology.covers_iff] at h ⊢
  exact J.superset_covering (Sieve.pullback_monotone f hAB) h

/-- La forme fleche est stable par borne superieure : si `S` couvre `f`,
    alors `S ⊔ R` couvre `f`.
    Preuve : cas particulier de `covers_mono` avec `le_sup_left`. -/
theorem covers_union {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) (S R : Sieve X) (hS : J.Covers S f) :
    J.Covers (S ⊔ R) f := by
  exact covers_mono J f (le_sup_left : S ≤ S ⊔ R) hS

/-!
## Section 2 : changement de base et isomorphismes

La loi de composition de `Sieve.pullback` (`Sieve.pullback_comp`) exprime le
changement de base : `S.pullback (g ≫ f) = (S.pullback f).pullback g`.
On en deduit la forme fleche du changement de base (`covers_pullback_comp`)
et la cancellation par isomorphisme (`covers_iso_cancel`), qui utilise le
lemme Mathlib `pullback_mem_iff_of_isIso`.
-/

/-- Loi de changement de base en forme fleche : couvrir la composee `g ≫ f`
    est equivalent a couvrir le pullback `S.pullback f` le long de `g`.
    Preuve : `covers_iff` des deux membres puis `Sieve.pullback_comp`
    (egalite definitionnelle des deux cribles en cause). -/
theorem covers_pullback_comp {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (f : Y ⟶ X) (g : Z ⟶ Y) (S : Sieve X) :
    J.Covers S (g ≫ f) ↔ J.Covers (S.pullback f) g := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    Sieve.pullback_comp]

/-- Cancellation par isomorphisme : si `g` est un isomorphisme, couvrir
    `g ≫ f` est equivalent a couvrir `f`.
    Preuve : changement de base (`Sieve.pullback_comp`) puis
    `pullback_mem_iff_of_isIso`, qui ramene le pullback le long d'une iso a
    l'appartenance d'origine. -/
theorem covers_iso_cancel {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (f : Y ⟶ X) {g : Z ⟶ Y} [IsIso g] (S : Sieve X) :
    J.Covers S (g ≫ f) ↔ J.Covers S f := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    Sieve.pullback_comp]
  exact GrothendieckTopology.pullback_mem_iff_of_isIso (i := g) (S := S.pullback f)

/-- Une fleche isomorphe `e.hom` est couverte par `S` si et seulement si
    `S` est couvrant.
    Preuve : `covers_iff` puis `pullback_mem_iff_of_isIso`. -/
theorem covers_iso_covering {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (e : X ≅ Y) (S : Sieve Y) :
    J.Covers S e.hom ↔ S ∈ J Y := by
  rw [GrothendieckTopology.covers_iff]
  exact GrothendieckTopology.pullback_mem_iff_of_isIso (S := S)

/-!
## Section 3 : caractere local

L'axiome de transitivite `arrow_trans` dit : si `S` couvre `f` et toute
fleche de `S` est couverte par `R`, alors `R` couvre `f`. La forme "lie"
`Sieve.bind S R` recolle les cribles `R g` en un seul crible sur `X` ; on
montre qu'il herite la couverture de `f`. La brique est la loi d'adjonction
`Sieve.le_pullback_bind : R g ≤ (Sieve.bind S R).pullback g` (le pullback du
lie contient chaque composante).
-/

/-- Caractere local en forme fleche : si `S` couvre `f` et, pour chaque
    fleche `g : Z ⟶ X` de `S`, le crible `R g` est couvrant sur son domaine
    (`R hg ∈ J Z`), alors le crible lie `Sieve.bind S R` couvre `f`.
    Preuve : `arrow_trans` de `S` vers `Sieve.bind S R`, puis pour chaque
    fleche `g` de `S`, `superset_covering` avec
    `Sieve.le_pullback_bind` (chaque `R g` est inferieure au pullback du lie). -/
theorem covers_bind {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) (S : Sieve X) (R : ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄, S g → Sieve Z)
    (hS : J.Covers S f) (hR : ∀ ⦃Z : C⦄ (g : Z ⟶ X) (hg : S g), R hg ∈ J Z) :
    J.Covers (Sieve.bind S R) f := by
  refine GrothendieckTopology.arrow_trans (J := J) (f := f) (S := S) (R := Sieve.bind S R) hS ?_
  intro Z g hg
  rw [GrothendieckTopology.covers_iff]
  exact J.superset_covering (Sieve.le_pullback_bind S R g hg) (hR g hg)

/-!
## Section 4 : pont vers la couverture bundlee

La couverture bundlee `J.Cover X = { S : Sieve X // S ∈ J X }` (Partie 38)
regroupe les cribles couvrants avec leur preuve d'appartenance. On relie la
forme fleche au sous-type : `S` couvre `f` si et seulement si le pullback
`S.pullback f` contient une couverture.
-/

/-- `S` couvre `f` si et seulement si `S.pullback f` contient un
    `J.Cover Y` (comme sous-crible).
    Preuve : direction directe — la couverture `S.pullback f` elle-meme est
    une `J.Cover Y` (`covers_iff`) ; direction reciproque —
    `superset_covering` depuis la couverture contenue. -/
theorem covers_iff_exists_cover {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S : Sieve X) (f : Y ⟶ X) :
    J.Covers S f ↔ ∃ T : J.Cover Y, (T : Sieve Y) ≤ S.pullback f := by
  constructor
  · intro h
    exact ⟨⟨S.pullback f, by simpa [GrothendieckTopology.covers_iff] using h⟩, le_rfl⟩
  · rintro ⟨T, hT⟩
    rw [GrothendieckTopology.covers_iff]
    exact J.superset_covering hT T.condition

/-- Le pullback d'une couverture `S.pullback f` couvre l'identite de `Y`.
    Preuve : `covers_iff` puis `Sieve.pullback_id` (le pullback de
    l'identite est l'identite) et la condition du sous-type. -/
theorem cover_pullback_covers {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S : J.Cover X) (f : Y ⟶ X) :
    J.Covers (S.pullback f) (𝟙 Y) := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_id]
  exact (S.pullback f).condition

end Grothendieck.CoversPullback

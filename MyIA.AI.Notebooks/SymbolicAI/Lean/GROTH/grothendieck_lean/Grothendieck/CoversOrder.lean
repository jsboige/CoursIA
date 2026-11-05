/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 41 : lois d'ordre de la forme flèche

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-40 ont etabli les fondamentaux : categories, cribles,
topologies, lois de treillis, identites de pullback, bases de faisceaux,
cloture couvrante, calibration, sous-canonicalite, topologies denses,
faisceaux, hom interne, cohomologie de Cech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, equivalences, categories monoidales,
limites et colimites, couples comma, images directes, theoremes propres sur la
forme fleche (`J.Covers S f`), sur la couverture bundlee (`J.Cover X`), les
lois de coherence du pseudo-foncteur pullback (Partie 37), les lois de
foncteur du pullback (Partie 38), les lois de treillis des topologies
(Partie 39) et les lois de la forme fleche sous pullback (Partie 40).

La Partie 41 etablit les **lois d'ordre de la forme fleche `J.Covers S f`** :
Mathlib fournit les axiomes de topologie en forme fleche (`arrow_max`,
`arrow_stable`, `arrow_trans`, `arrow_intersect`), le definitif `covers_iff`,
la monotonie en le crible (`superset_covering`), la loi de pullback
(`pullback_stable`) et la loi de treillis `pullback_inter`, mais **ne fournit
pas** le comportement de `J.Covers` vis-a-vis des bornes du treillis des
cribles (haut, bas, intersection), la stabilite de toute couverture, la
connexion a la generation `Sieve.generate`, ni la compatibilite du pullback
avec l'intersection. Ce module les enonce et les prouve :

  - `covers_top` : le crible haut couvre toute fleche.
  - `covers_bot_iff` : le crible bas couvre `f` si et seulement s'il est
    couvrant sur le codomaine.
  - `covers_of_covering` : une couverture de `X` couvre toute fleche vers
    `X` (forme flèche de `pullback_stable`).
  - `covers_inter_iff` : `S ⊓ R` couvre `f` si et seulement si `S` et `R`
    couvrent `f` (reciproque de `arrow_intersect`).
  - `covers_generate_sieve` : couvrir le crible genere `Sieve.generate S`
    equivaut a couvrir `S` (un crible est egal au crible qu'il genere).
  - `covers_pullback_inter` : le pullback de `S ⊓ R` le long de `g ≫ f`
    couvre exactement l'intersection des pullbacks (loi de compatibilite
    pullback / intersection en forme flèche).

Chaque preuve est une **preuve tactique reelle** (veine DEEP) : les axiomes
de topologie (`top_mem`, `pullback_stable`, `superset_covering`,
`arrow_intersect`) plus les lois de `Sieve.pullback` (`pullback_top`,
`pullback_bot`, `pullback_comp`, `pullback_inter`) et la generation
(`Sieve.generate_sieve`). Aucune preuve n'est un re-export.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s elimines a la creation.

### Convention i18n (EPIC #4980 ratifiee par user 2026-07-04)

Ce module est apparie avec son jumeau anglais dans le fichier sibling
`CoversOrder_en.lean` (modele sibling pair, voir PR #6154 pour le pilote sur
`Utility.lean`). Namespace suffix `_en` applique au fichier EN (anti-collision,
conforme code-style.md #4980). Les enonces de theoremes, les noms de lemmes,
les tactiques Lean et les references Mathlib restent en anglais ; seules les
docstrings `/-- ... -/` et les commentaires `-- ...` different entre les deux
fichiers (preservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversOrder

open CategoryTheory

/-!
## Section 1 : bornes du treillis des cribles

Le crible haut `⊤` est couvrant (`top_mem`) ; par definition de la forme
fleche (`covers_iff`) et `Sieve.pullback_top`, il couvre toute fleche. Le
crible bas `⊥` est un cas symetrique : son pullback est le bas, donc il ne
couvre que s'il est deja couvrant sur le codomaine.
-/

/-- Le crible haut couvre toute fleche : `J.Covers ⊤ f` pour tout `f`.
    Preuve : `covers_iff` puis `Sieve.pullback_top`, et `top_mem`. -/
theorem covers_top {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (f : Y ⟶ X) : J.Covers (⊤ : Sieve X) f := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_top]
  exact J.top_mem Y

/-- Le crible bas couvre `f : Y ⟶ X` si et seulement s'il est couvrant
    sur `Y` : `J.Covers ⊥ f ↔ ⊥ ∈ J Y`.
    Preuve : `covers_iff` puis `Sieve.pullback_bot` (le pullback du bas est
    le bas). -/
theorem covers_bot_iff {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (f : Y ⟶ X) :
    J.Covers (⊥ : Sieve X) f ↔ ⊥ ∈ J Y := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_bot]

/-!
## Section 2 : stabilite d'une couverture

L'axiome `pullback_stable` dit que le pullback d'une couverture est une
couverture. La forme fleche en est la reformulation directe : une couverture
de `X` couvre toute fleche vers `X`.
-/

/-- Une couverture de `X` couvre toute fleche vers `X` :
    `S ∈ J X → J.Covers S f` (forme flèche de `pullback_stable`).
    Preuve : `covers_iff` puis l'axiome `J.pullback_stable`. -/
theorem covers_of_covering {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) {S : Sieve X} (hS : S ∈ J X) (f : Y ⟶ X) :
    J.Covers S f := by
  rw [GrothendieckTopology.covers_iff]
  exact J.pullback_stable f hS

/-!
## Section 3 : intersection

L'axiome `arrow_intersect` fournit `J.Covers S f → J.Covers R f →
J.Covers (S ⊓ R) f`. La loi `Sieve.pullback_inter` (le pullback d'une
intersection est l'intersection des pullbacks) donne la reciproque : si
`S ⊓ R` couvre `f`, alors chaque facteur couvre `f`.
-/

/-- `S ⊓ R` couvre `f` si et seulement si `S` et `R` couvrent `f`.
    Preuve : direction directe — `arrow_intersect` ; direction reciproque —
    `covers_iff`, `Sieve.pullback_inter`, puis `superset_covering` avec
    `inf_le_left` et `inf_le_right`. -/
theorem covers_inter_iff {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S R : Sieve X) (f : Y ⟶ X) :
    J.Covers (S ⊓ R) f ↔ J.Covers S f ∧ J.Covers R f := by
  constructor
  · intro h
    rw [GrothendieckTopology.covers_iff] at h ⊢
    rw [Sieve.pullback_inter] at h
    exact ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩
  · rintro ⟨hS, hR⟩
    exact GrothendieckTopology.arrow_intersect (J := J) (f := f) (S := S) (R := R) hS hR

/-!
## Section 4 : generation et pullback

Un crible est egal au crible qu'il genere (`Sieve.generate_sieve`) ; couvrir
l'un equivaut a couvrir l'autre. Enfin, le pullback d'une intersection le
long d'une composee se factorise : `(S ⊓ R).pullback (g ≫ f)` est le pullback
de l'intersection des pullbacks.
-/

/-- Couvrir le crible genere `Sieve.generate S` equivaut a couvrir `S`.
    Preuve : `covers_iff` des deux membres puis `Sieve.generate_sieve`. -/
theorem covers_generate_sieve {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S : Sieve X) (f : Y ⟶ X) :
    J.Covers (Sieve.generate S) f ↔ J.Covers S f := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    Sieve.generate_sieve]

/-- Compatibilite pullback / intersection en forme fleche : `S ⊓ R` couvre
    `g ≫ f` si et seulement si `S.pullback f ⊓ R.pullback f` couvre `g`.
    Preuve : `covers_iff` des deux membres, `Sieve.pullback_comp` (changement
    de base de la composee) puis `Sieve.pullback_inter` (le pullback d'une
    intersection est l'intersection des pullbacks). -/
theorem covers_pullback_inter {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (S R : Sieve X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    J.Covers (S ⊓ R) (g ≫ f) ↔ J.Covers (S.pullback f ⊓ R.pullback f) g := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    Sieve.pullback_comp, ← Sieve.pullback_inter]

end Grothendieck.CoversOrder

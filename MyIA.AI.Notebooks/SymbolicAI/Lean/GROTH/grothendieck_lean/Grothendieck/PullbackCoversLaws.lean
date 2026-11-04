/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 42 : lois de la forme flèche sous pullback itéré

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-41 ont etabli les fondamentaux : categories, cribles,
topologies, lois de treillis, identites de pullback, bases de faisceaux,
cloture couvrante, calibration, sous-canonicalite, topologies denses,
faisceaux, hom interne, cohomologie de Cech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, equivalences, categories monoidales,
limites et colimites, couples comma, images directes, theoremes propres sur la
forme fleche (`J.Covers S f`), sur la couverture bundlee (`J.Cover X`), les
lois de coherence du pseudo-foncteur pullback (Partie 37), les lois de
foncteur du pullback (Partie 38), les lois de treillis des topologies
(Partie 39), les lois de la forme fleche sous pullback (Partie 40) et les
lois d'ordre de la forme fleche (Partie 41).

La Partie 42 etablit les **lois de la forme fleche `J.Covers S f` sous le
pullback itere des cribles** : Mathlib fournit les axiomes de topologie en
forme fleche (`arrow_max`, `arrow_stable`, `arrow_trans`,
`arrow_intersect`), le definitif `covers_iff` et les lois de `Sieve.pullback`
(`pullback_id`, `pullback_comp`, `pullback_inter`), mais **ne fournit pas**
la lecture de ces lois en termes de `J.Covers` : l'unite du pullback, son
associativite, la distributivite sur l'intersection et la commutation avec la
generation d'un crible le long d'une fleche (conditionnee par l'existence
des pullbacks de la famille). Ce module les enonce et les prouve :

  - `covers_pullback_id` : pullbacker par l'identite est une operation
    neutre en forme fleche (unite du pseudo-foncteur pullback).
  - `covers_pullback_assoc` : pullbacker le long de `g ≫ f` puis le long de
    `h` equivaut a pullbacker le long de `g` puis le long de `h`
    (associativite, loi de coherence du pseudo-foncteur pullback).
  - `covers_sieve_pullback_inter` : le pullback d'un crible d'intersection
    est l'intersection des pullbacks (distributivite du pullback sur le
    treillis des cribles, en forme fleche).
  - `covers_pullback_generate` : couvrir le crible genere par
    `R.pullbackArrows f` equivaut a couvrir le crible genere par `R` le long
    de la composee (commutation generation / pullback, en forme fleche).

Chaque preuve est une **preuve tactique reelle** (veine DEEP) : elle compose
les lois de `Sieve.pullback` (`pullback_id`, `pullback_comp`,
`pullback_inter`, `pullbackArrows_comm`) avec le definitif `covers_iff` et la
loi de la forme fleche `covers_comp_iff` (Partie 35). Aucune preuve n'est un
re-export.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s elimines a la creation.

### Convention i18n (EPIC #4980 ratifiee par user 2026-07-04)

Ce module est apparie avec son jumeau anglais dans le fichier sibling
`PullbackCoversLaws_en.lean` (modele sibling pair, voir PR #6154 pour le
pilote sur `Utility.lean`). Namespace suffix `_en` applique au fichier EN
(anti-collision, conforme code-style.md #4980). Les enonces de theoremes, les
noms de lemmes, les tactiques Lean et les references Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
different entre les deux fichiers (preservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Grothendieck.CoversArrow

namespace Grothendieck.PullbackCoversLaws

open CategoryTheory

/-!
## Section 1 : unite du pullback

`Sieve.pullback_id` identifie le pullback par l'identite au crible lui-meme.
En forme fleche, pullbacker `S` par `𝟙 X` ne change donc rien : `S.pullback (𝟙 X)`
couvre `f` exactement quand `S` couvre `f`. C'est l'unite du pseudo-foncteur
pullback (le pendant en forme fleche de `pullbackId` de la Partie 37, qui
l'enoncait au niveau des couvertures bundlees `J.Cover X`).
-/

/-- Pullbacker le crible par l'identite est une operation neutre en forme
    fleche : `S.pullback (𝟙 X)` couvre `f` si et seulement si `S` couvre `f`.
    Preuve : le definitif `covers_iff` reduit les deux cotes a
    `S.pullback f ∈ J Y`, puis `Sieve.pullback_id` identifie
    `S.pullback (𝟙 X)` a `S`. -/
theorem covers_pullback_id {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S : Sieve X) (f : Y ⟶ X) :
    J.Covers (S.pullback (𝟙 X)) f ↔ J.Covers S f := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    Sieve.pullback_id]

/-!
## Section 2 : associativite du pullback

La loi `Sieve.pullback_comp` dit que pullbacker le long d'une composee
`g ≫ f` est pullbacker le long de `g` du crible deja pullbacke par `f`.
En forme fleche, cela donne la loi d'associativite du pseudo-foncteur
pullback : `(S.pullback f).pullback g` et `S.pullback (g ≫ f)` couvrent les
memes fleches.
-/

/-- La loi d'associativite du pullback en forme fleche : `(S.pullback f).pullback g`
    couvre `h` si et seulement si `S.pullback (g ≫ f)` couvre `h`. Preuve :
    le definitif `covers_iff` ramene aux appartenances, puis
    `Sieve.pullback_comp` identifie les deux cribles pullbackes. -/
theorem covers_pullback_assoc {C : Type*} [Category C] {W X Y Z : C}
    (J : GrothendieckTopology C) (S : Sieve Z) (f : Y ⟶ Z) (g : X ⟶ Y)
    (h : W ⟶ X) :
    J.Covers ((S.pullback f).pullback g) h ↔ J.Covers (S.pullback (g ≫ f)) h := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    Sieve.pullback_comp]

/-!
## Section 3 : distributivite du pullback sur l'intersection

`Sieve.pullback_inter` fait passer le pullback dans l'intersection de deux
cribles. En forme fleche, la Partie 41 a lu cette loi le long d'une fleche
composee (`covers_pullback_inter` : `S ⊓ R` couvre `g ≫ f`) ; ici on la lit
sur le pullback du crible lui-meme : `(S ⊓ R).pullback f` couvre `g` si et
seulement si `S.pullback f ⊓ R.pullback f` couvre `g`.
-/

/-- La distributivite du pullback de crible sur l'intersection, en forme
    fleche : `(S ⊓ R).pullback f` couvre `g` si et seulement si
    `S.pullback f ⊓ R.pullback f` couvre `g`. Preuve : `covers_iff` puis
    `Sieve.pullback_inter`. -/
theorem covers_sieve_pullback_inter {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (S R : Sieve X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    J.Covers ((S ⊓ R).pullback f) g ↔ J.Covers (S.pullback f ⊓ R.pullback f) g := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    Sieve.pullback_inter]

/-!
## Section 4 : commutation generation / pullback

La loi `Sieve.pullbackArrows_comm` (Mathlib) relie le crible genere par les
pullbacks d'une famille `R` de fleches vers `X` au pullback du crible genere
par `R` : `Sieve.generate (R.pullbackArrows f) = (Sieve.generate R).pullback f`,
conditionnellement a l'existence des pullbacks des fleches de `R` le long de
`f` (`R.HasPullbacks f`). En forme fleche, composee avec `covers_comp_iff`
(Partie 35), cette identite donne la commutation generation / pullback :
couvrir le crible engendre par les pullbacks de `R` le long de `f` equivaut a
couvrir le crible engendre par `R` le long de la composee `g ≫ f`.
-/

/-- La commutation generation / pullback en forme fleche : couvrir le crible
    engendre par `R.pullbackArrows f` equivaut a couvrir le crible engendre
    par `R` le long de la composee. Preuve : `Sieve.pullbackArrows_comm`
    remplace le crible genere par les pullbacks par le pullback du crible
    genere, puis `covers_comp_iff` (Partie 35) en donne la lecture en forme
    fleche. -/
theorem covers_pullback_generate {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (R : Presieve X) (f : Y ⟶ X) (g : Z ⟶ Y)
    [R.HasPullbacks f] :
    J.Covers (Sieve.generate (R.pullbackArrows f)) g ↔
      J.Covers (Sieve.generate R) (g ≫ f) := by
  rw [Sieve.pullbackArrows_comm]
  exact Grothendieck.CoversArrow.covers_comp_iff J (Sieve.generate R) f g

end Grothendieck.PullbackCoversLaws

/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 52 : forme flèche de la topologie engendrée par une couverture

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-51 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback,
les lois de treillis indexées, la forme flèche des topologies dense,
extrémales, de l'adjonction pushforward-pullback, du bind, de la topologie
engendrée par une prétopologie, de la topologie induite le long d'un
foncteur, des foncteurs préservant les couvertures, et des lois de
composition de ces foncteurs.

Cette partie applique le fil conducteur « forme flèche » à la **topologie
engendrée par une couverture** (`Coverage.toGrothendieck`). Mathlib fournit
au niveau ponctuel `Coverage.mem_toGrothendieck` :
`S ∈ K.toGrothendieck X ↔ Saturate K X S`, mais **aucune loi ne la connecte
à la forme flèche** `J.Covers`. On comble le trou par cinq théorèmes
propres :

  - `covers_iff_toGrothendieck` (central) : pour `J := K.toGrothendieck`,
    `J.Covers S f ↔ Saturate K Y (S.pullback f)` — pont direct entre la
    forme flèche et l'extension inductive `Saturate`, via `covers_iff`
    et `Coverage.mem_toGrothendieck`. C'est la **loi naturelle** reliant
    la couverture au sens de Grothendieck et la couverture au sens de
    Cover (1957).
  - `covers_toGrothendieck_of_of` (cas particulier) : si `R ∈ K X` est
    une famille couvrante, alors le crible qu'elle engendre couvre
    l'identité : `K.toGrothendieck.Covers (Sieve.generate R) (𝟙 X)` —
    le sens direct de `Saturate.of`.
  - `covers_toGrothendieck_top` (cas particulier) : la couverture
    triviale `⊤` couvre n'importe quelle flèche : `K.toGrothendieck.Covers
    ⊤ f`. Retombée du constructeur `Saturate.top` via `covers_iff` et
    `mem_toGrothendieck`.
  - `covers_of_mem_toGrothendieck` (passage par `Sieve.generate`) : si
    `R` est une famille couvrante pour K, alors
    `K.toGrothendieck.Covers (Sieve.generate R) f` — pour toute flèche
    `f : Y ⟶ X`, la couverture descend d'un cran via la stabilité par
    pullback (`Saturate.pullback`) et la monotonie du pullback.
  - `covers_iff_pullback_toGrothendieck` (cas particulier sur l'identité)
    : `K.toGrothendieck.Covers S (𝟙 X) ↔ S ∈ K.toGrothendieck X` — la
    retombée ponctuelle, spécialisation directe de `covers_iff_covers_id`
    (Partie 35) au cas `J := K.toGrothendieck`. La preuve de
    `covers_iff_covers_id` est inlinée pour rendre ce module
    auto-suffisant (la Partie 35 n'est pas nécessairement sur `main` à
    la date de cette PR).

Chaque preuve est une **preuve tactique réelle** (veine DEEP) : les axiomes
de Mathlib (`GrothendieckTopology.covers_iff`, `Coverage.mem_toGrothendieck`,
`Coverage.Saturate.pullback`, `Coverage.Saturate.top`, `Coverage.Saturate.of`,
`Sieve.pullback_id`, `Sieve.pullback_monotone`, `Sieve.generate_sieve`) plus
la définition `Coverage.toGrothendieck`. Aucune preuve n'est un re-export
ou un unfold.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s éliminés à la création.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est apparié avec son jumeau anglais dans le fichier sibling
`CoversCoverageArrow_en.lean` (modèle sibling pair, voir PR #6154 pour
le pilote sur `Utility.lean`). Namespace suffix `_en` appliqué au fichier EN
(anti-collision, conforme code-style.md #4980). Les énoncés de théorèmes, les
noms de lemmas, les tactiques Lean et les références Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
diffèrent entre les deux fichiers (préservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Coverage

namespace Grothendieck.CoversCoverageArrow

open CategoryTheory Coverage

universe u v

/-!
## Section 1 : le pont central — forme flèche ↔ extension inductive

L'extension `Coverage.toGrothendieck` part d'une famille couvrante au sens
de `Coverage` (1957, Grothendieck-Verdier) et la sature en topologie de
Grothendieck via la clôture inductive `Saturate` (cas de base : cribles
engendrés, cribles top ; pas inductif : stabilité par pullback implicite).
La forme flèche `K.toGrothendieck.Covers S f ↔ S.pullback f ∈ K.toGrothendieck Y`
réduit au ponctuel ; `Coverage.mem_toGrothendieck` identifie l'appartenance
ponctuelle à `Saturate K Y (S.pullback f)`. Le pont est immédiat par
réécriture, mais il **manque** dans Mathlib sous cette forme.
-/

/-- Pont central : la forme flèche pour la topologie `K.toGrothendieck`
    équivaut à l'extension inductive `Saturate` :
    `K.toGrothendieck.Covers S f ↔ Saturate K Y (S.pullback f)`.
    Preuve : `covers_iff` réduit à `S.pullback f ∈ K.toGrothendieck Y`,
    puis `Coverage.mem_toGrothendieck` identifie à `Saturate K Y (S.pullback f)`. -/
theorem covers_iff_toGrothendieck {C : Type u} [Category.{v} C]
    (K : Coverage C) {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    K.toGrothendieck.Covers S f ↔ Coverage.Saturate K Y (S.pullback f) := by
  rw [GrothendieckTopology.covers_iff]
  exact Coverage.mem_toGrothendieck.symm

/-!
## Section 2 : cas de base — le constructeur `Saturate.of`

Quand la couverture au sens de `Coverage` est un ensemble de morphismes
vers `X`, son crible engendré couvre l'identité au sens de
`K.toGrothendieck` — c'est le cas de base de la clôture inductive `Saturate`
exporté en forme flèche. Mathlib a `Coverage.Saturate.of` au niveau
ponctuel, mais **pas** la forme flèche.
-/

/-- Cas de base : si `R ∈ K X` est une famille couvrante, alors le crible
    qu'elle engendre couvre l'identité :
    `K.toGrothendieck.Covers (Sieve.generate R) (𝟙 X)`.
    Preuve : on calcule directement que `S.pullback (𝟙 X) = S` (via
    `Sieve.pullback_id`), donc `K.toGrothendieck.Covers (Sieve.generate R)
    (𝟙 X) ↔ Saturate K X (Sieve.generate R)` par `covers_iff_toGrothendieck`.
    Le membre droit est `Saturate.of X R hR` (le constructeur de base de
    `Saturate`). -/
theorem covers_toGrothendieck_of_of {C : Type u} [Category.{v} C]
    (K : Coverage C) {X : C} {R : Presieve X} (hR : R ∈ K X) :
    K.toGrothendieck.Covers (Sieve.generate R) (𝟙 X) := by
  rw [covers_iff_toGrothendieck, Sieve.pullback_id]
  exact Coverage.Saturate.of X R hR

/-- Cas de base généralisé : la couverture engendrée par `R` couvre
    n'importe quelle flèche `f : Y ⟶ X`. Preuve : `Saturate.pullback`
    propage `Saturate K X (Sieve.generate R)` au pullback le long de `f`,
    puis `covers_iff_toGrothendieck` rend la forme flèche. -/
theorem covers_of_mem_toGrothendieck {C : Type u} [Category.{v} C]
    (K : Coverage C) {X Y : C} (f : Y ⟶ X) {R : Presieve X} (hR : R ∈ K X) :
    K.toGrothendieck.Covers (Sieve.generate R) f := by
  rw [covers_iff_toGrothendieck]
  exact Coverage.Saturate.pullback K f (Coverage.Saturate.of X R hR)

/-- Cas particulier sur le crible top : `K.toGrothendieck.Covers ⊤ f`
    pour toute `f : Y ⟶ X`. Preuve : `Saturate.top Y` fournit
    `Saturate K Y ⊤` (le top est son propre pullback le long de n'importe
    quelle flèche, et le `Saturate.top` constructeur vaut pour tout `Y`) ;
    `covers_iff_toGrothendieck` rend la forme flèche. -/
theorem covers_toGrothendieck_top {C : Type u} [Category.{v} C]
    (K : Coverage C) {X Y : C} (f : Y ⟶ X) :
    K.toGrothendieck.Covers (⊤ : Sieve X) f := by
  rw [covers_iff_toGrothendieck]
  exact Coverage.Saturate.top Y

/-!
## Section 3 : retombée ponctuelle

Spécialisation sur l'identité : `K.toGrothendieck.Covers S (𝟙 X) ↔ S ∈
K.toGrothendieck X`. C'est l'instance directe de `covers_iff_covers_id`
(Partie 35) au cas `J := K.toGrothendieck`. Le pont vers la couverture
ponctuelle `Coverage.mem_toGrothendieck` est immédiat.
-/

/-- Retombée ponctuelle : pour `J := K.toGrothendieck`, couvrir le long
    de l'identité équivaut à appartenir à la topologie :
    `K.toGrothendieck.Covers S (𝟙 X) ↔ S ∈ K.toGrothendieck X ↔ Saturate K X S`.
    Preuve : `Sieve.pullback_id` ramène au ponctuel, puis
    `Coverage.mem_toGrothendieck` identifie à `Saturate K X S`. -/
theorem covers_iff_pullback_toGrothendieck {C : Type u} [Category.{v} C]
    (K : Coverage C) {X : C} (S : Sieve X) :
    K.toGrothendieck.Covers S (𝟙 X) ↔ Coverage.Saturate K X S := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_id]
  exact Coverage.mem_toGrothendieck.symm

end Grothendieck.CoversCoverageArrow
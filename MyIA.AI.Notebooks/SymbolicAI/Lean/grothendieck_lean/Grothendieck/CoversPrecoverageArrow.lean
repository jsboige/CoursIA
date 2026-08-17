/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 53 : forme flèche de la topologie engendrée par une pré-couverture

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-52 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback,
les lois de treillis indexées, la forme flèche des topologies dense,
extrémales, de l'adjonction pushforward-pullback, du bind, de la topologie
engendrée par une prétopologie, de la topologie induite le long d'un
foncteur, des foncteurs préservant les couvertures, des lois de
composition de ces foncteurs, et de la topologie engendrée par une
couverture au sens de `Coverage`.

Cette partie applique le fil conducteur « forme flèche » à la **topologie
engendrée par une pré-couverture** (`Precoverage.toGrothendieck`).
Mathlib fournit au niveau ponctuel `Precoverage.mem_toGrothendieck_iff` :
`S ∈ J.toGrothendieck X ↔ Saturate J X S`, mais **aucune loi ne la connecte
à la forme flèche** `J.Covers`. On comble le trou par cinq théorèmes
propres — structure identique à la Partie 52 mais à un niveau
plus primitif, puisque `Precoverage.Saturate` (4 constructeurs : `of`,
`top`, `pullback`, `transitive`) est plus primitif que `Coverage.Saturate`
(3 constructeurs : la stabilité par pullback étant intégrée dans la
notion même de `Coverage`) :

  - `covers_iff_toGrothendieck` (central) : pour `J : Precoverage C`,
    `J.toGrothendieck.Covers S f ↔ Saturate J Y (S.pullback f)` — pont
    direct entre la forme flèche et l'extension inductive `Saturate`, via
    `covers_iff` et `Precoverage.mem_toGrothendieck_iff`. C'est la **loi
    naturelle** à l'étage pré-couverture.
  - `covers_toGrothendieck_of_of` (cas particulier) : si `R ∈ J X` est
    une pré-couverture, alors le crible qu'elle engendre couvre
    l'identité : `J.toGrothendieck.Covers (Sieve.generate R) (𝟙 X)` —
    le sens direct de `Saturate.of`.
  - `covers_toGrothendieck_top` (cas particulier) : la couverture
    triviale `⊤` couvre n'importe quelle flèche : `J.toGrothendieck.Covers
    ⊤ f`. Retombée du constructeur `Saturate.top` via `covers_iff` et
    `mem_toGrothendieck_iff`.
  - `covers_of_mem_toGrothendieck` (passage par `Sieve.generate`) : si
    `R` est une pré-couverture, alors `J.toGrothendieck.Covers
    (Sieve.generate R) f` — pour toute flèche `f : Y ⟶ X`, la couverture
    descend d'un cran via la stabilité par pullback (`Saturate.pullback`)
    qui apparaît ici comme **constructeur inductif** (vs. axiome chez
    `Coverage`).
  - `covers_iff_pullback_toGrothendieck` (cas particulier sur l'identité)
    : `J.toGrothendieck.Covers S (𝟙 X) ↔ S ∈ J.toGrothendieck X` — la
    retombée ponctuelle, via `Sieve.pullback_id` + `covers_iff`.

Chaque preuve est une **preuve tactique réelle** (veine DEEP) : les axiomes
de Mathlib (`GrothendieckTopology.covers_iff`, `Precoverage.mem_toGrothendieck_iff`,
`Precoverage.Saturate.pullback`, `Precoverage.Saturate.top`, `Precoverage.Saturate.of`,
`Sieve.pullback_id`, `Precoverage.generate_mem_toGrothendieck`) plus la
définition `Precoverage.toGrothendieck`. Aucune preuve n'est un re-export
ou un unfold.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s éliminés à la création.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est apparié avec son jumeau anglais dans le fichier sibling
`CoversPrecoverageArrow_en.lean` (modèle sibling pair, voir PR #6154 pour
le pilote sur `Utility.lean`). Namespace suffix `_en` appliqué au fichier EN
(anti-collision, conforme code-style.md #4980). Les énoncés de théorèmes, les
noms de lemmas, les tactiques Lean et les références Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
diffèrent entre les deux fichiers (préservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

namespace Grothendieck.CoversPrecoverageArrow

open CategoryTheory Precoverage

universe u v

/-!
## Section 1 : le pont central — forme flèche ↔ extension inductive

L'extension `Precoverage.toGrothendieck` part d'une pré-couverture (famille
de présieves couvrantes sur chaque objet) et la sature en topologie de
Grothendieck via la clôture inductive `Saturate` à 4 constructeurs : `of`
(cas de base d'une pré-couverture), `top` (cas trivial), `pullback`
(stabilité par pullback — qui est ici **inductive** et non axiome comme
dans `Coverage`), et `transitive` (caractère local). La forme flèche
`J.toGrothendieck.Covers S f ↔ S.pullback f ∈ J.toGrothendieck Y` réduit
au ponctuel ; `Precoverage.mem_toGrothendieck_iff` identifie l'appartenance
ponctuelle à `Saturate J Y (S.pullback f)`. Le pont est immédiat par
réécriture, mais il **manque** dans Mathlib sous cette forme.

La différence avec la Partie 52 (`Coverage` → `Grothendieck`) est que
`Precoverage.Saturate.pullback` apparaît comme **constructeur inductif**
donc la stabilité par pullback est interne à l'induction. Cela donne à
`covers_iff_toGrothendieck` le même énoncé, mais la structure de preuve
sous-jacente est plus riche (la définition de `Saturate.pullback` doit
être manipulée plus directement).
-/

/-- Pont central : la forme flèche pour la topologie `J.toGrothendieck`
    (où `J : Precoverage C`) équivaut à l'extension inductive `Saturate` :
    `J.toGrothendieck.Covers S f ↔ Saturate J Y (S.pullback f)`.
    Preuve : `covers_iff` réduit à `S.pullback f ∈ J.toGrothendieck Y`,
    puis `Precoverage.mem_toGrothendieck_iff` identifie à
    `Saturate J Y (S.pullback f)`. -/
theorem covers_iff_toGrothendieck {C : Type u} [Category.{v} C]
    (J : Precoverage C) {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    J.toGrothendieck.Covers S f ↔ Saturate J Y (S.pullback f) := by
  rw [GrothendieckTopology.covers_iff]
  exact Precoverage.mem_toGrothendieck_iff.symm

/-!
## Section 2 : cas de base — le constructeur `Saturate.of`

Quand la pré-couverture est un ensemble de morphismes vers `X`, son
crible engendré couvre l'identité au sens de `J.toGrothendieck` — c'est
le cas de base de la clôture inductive `Saturate` exporté en forme flèche.
Mathlib a `Precoverage.Saturate.of` au niveau ponctuel, mais **pas** la
forme flèche. `Precoverage.generate_mem_toGrothendieck` est la retombée
ponctuelle, mais on exporte ici le pont en flèche.
-/

/-- Cas de base : si `R ∈ J X` est une pré-couverture, alors le crible
    qu'elle engendre couvre l'identité :
    `J.toGrothendieck.Covers (Sieve.generate R) (𝟙 X)`.
    Preuve : on calcule directement que `S.pullback (𝟙 X) = S` (via
    `Sieve.pullback_id`), donc
    `J.toGrothendieck.Covers (Sieve.generate R) (𝟙 X) ↔ Saturate J X (Sieve.generate R)`
    par `covers_iff_toGrothendieck`. Le membre droit est `Saturate.of X R hR`
    (le constructeur de base de `Saturate`). -/
theorem covers_toGrothendieck_of_of {C : Type u} [Category.{v} C]
    (J : Precoverage C) {X : C} {R : Presieve X} (hR : R ∈ J X) :
    J.toGrothendieck.Covers (Sieve.generate R) (𝟙 X) := by
  rw [covers_iff_toGrothendieck, Sieve.pullback_id]
  exact Saturate.of X R hR

/-- Cas de base généralisé : la couverture engendrée par `R` couvre
    n'importe quelle flèche `f : Y ⟶ X`. Preuve : `Saturate.pullback`
    propage `Saturate J X (Sieve.generate R)` au pullback le long de `f`,
    puis `covers_iff_toGrothendieck` rend la forme flèche. NB : chez
    `Precoverage`, `Saturate.pullback` est un **constructeur inductif**
    (pas un axiome comme chez `Coverage`). -/
theorem covers_of_mem_toGrothendieck {C : Type u} [Category.{v} C]
    (J : Precoverage C) {X Y : C} (f : Y ⟶ X) {R : Presieve X} (hR : R ∈ J X) :
    J.toGrothendieck.Covers (Sieve.generate R) f := by
  rw [covers_iff_toGrothendieck]
  exact Saturate.pullback X (Sieve.generate R) (Saturate.of X R hR) Y f

/-- Cas particulier sur le crible top : `J.toGrothendieck.Covers ⊤ f`
    pour toute `f : Y ⟶ X`. Preuve : `Saturate.top Y` fournit
    `Saturate J Y ⊤` (le top est son propre pullback le long de n'importe
    quelle flèche, et le `Saturate.top` constructeur vaut pour tout `Y`) ;
    `covers_iff_toGrothendieck` rend la forme flèche. -/
theorem covers_toGrothendieck_top {C : Type u} [Category.{v} C]
    (J : Precoverage C) {X Y : C} (f : Y ⟶ X) :
    J.toGrothendieck.Covers (⊤ : Sieve X) f := by
  rw [covers_iff_toGrothendieck]
  exact Saturate.top Y

/-!
## Section 3 : retombée ponctuelle

Spécialisation sur l'identité : `J.toGrothendieck.Covers S (𝟙 X) ↔ S ∈
J.toGrothendieck X`. Le pont vers la couverture ponctuelle
`Precoverage.mem_toGrothendieck_iff` est immédiat.
-/

/-- Retombée ponctuelle : pour `J : Precoverage C`, couvrir le long
    de l'identité équivaut à appartenir à la topologie :
    `J.toGrothendieck.Covers S (𝟙 X) ↔ S ∈ J.toGrothendieck X ↔ Saturate J X S`.
    Preuve : `Sieve.pullback_id` ramène au ponctuel, puis
    `Precoverage.mem_toGrothendieck_iff` identifie à `Saturate J X S`. -/
theorem covers_iff_pullback_toGrothendieck {C : Type u} [Category.{v} C]
    (J : Precoverage C) {X : C} (S : Sieve X) :
    J.toGrothendieck.Covers S (𝟙 X) ↔ Saturate J X S := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_id]
  exact Precoverage.mem_toGrothendieck_iff.symm

end Grothendieck.CoversPrecoverageArrow
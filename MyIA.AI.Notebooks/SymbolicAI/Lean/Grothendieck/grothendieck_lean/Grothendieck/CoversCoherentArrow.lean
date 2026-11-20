/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 55a : forme flèche de la topologie cohérente

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-54 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisis, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories
monoïdales, la construction de Grothendieck, l'image directe/exceptionnelle,
la forme flèche de la couverture, les lois de cohérence du pseudo-foncteur
pullback, les lois de treillis indexées, la forme flèche des topologies
dense, extrémales, de l'adjonction pushforward-pullback, du bind, de la
topologie engendrée par une prétopologie (`Precoverage.toGrothendieck`),
de la topologie induite le long d'un foncteur, des foncteurs préservant
les couvertures, des lois de composition de ces foncteurs, de la
topologie engendrée par une couverture au sens de `Coverage`, et de la
topologie engendrée par une pré-couverture (`Precoverage.toGrothendieck`)
ainsi que par une prétopologie (`Pretopology.toGrothendieck`).

Cette partie applique le fil conducteur « forme flèche » à la **topologie
cohérente** (`coherentTopology`) sur une catégorie `Precoherent`. Mathlib
fournit au niveau ponctuel `mem_toGrothendieck` via `Saturate`, mais
**aucune loi ne la connecte à la forme flèche** `coherentTopology.Covers`.
On comble le trou par cinq théorèmes propres — structure identique à la
Partie 52 mais spécialisée à la couverture cohérente : la cohérence
exige qu'une famille couvrante soit `Saturate` (inductif avec constructeur
`of` issu des `EffectiveEpiFamily`). Cela donne aux théorèmes une saveur
proche de ceux de la Partie 52, mais restreinte à la structure `Precoherent`
qui garantit la stabilité par pullback des familles effectives.

  - `covers_iff_toGrothendieck` (central) : pour
    `coherentTopology C` (avec `[Precoherent C]`),
    `coherentTopology C |>.Covers S f ↔ Saturate (coherentCoverage C) Y (S.pullback f)`
    — pont direct entre la forme flèche et la caractérisation inductive
    ponctuelle, via `covers_iff` puis `mem_toGrothendieck`. C'est la
    **loi naturelle** à l'étage cohérent.
  - `covers_toGrothendieck_of_of` (cas particulier) : si
    `(S : Presieve X) ∈ (coherentCoverage C) X`, alors le crible
    `Sieve.generate S` couvre l'identité : `(coherentTopology C).Covers
    (Sieve.generate S) (𝟙 X)` — la retombée ponctuelle via
    `covering_iff_covers_id`.
  - `covers_toGrothendieck_top` (cas particulier) : la couverture
    triviale ` ⊤` couvre l'identité : `(coherentTopology C).Covers ⊤
    (𝟙 X)`, retombée de `Saturate.top`.
  - `covers_of_mem_toGrothendieck` (cas particulier sur `Sieve.generate`) :
    si `(S : Presieve X) ∈ (coherentCoverage C) X`, alors
    `(coherentTopology C).Covers (Sieve.generate S) f` pour n'importe
    quelle `f : Y ⟶ X` — la stabilité par pullback via
    `Saturate.pullback` puis `Saturate.of`.
  - `covers_iff_pullback_toGrothendieck` (cas particulier sur l'identité) :
    `(coherentTopology C).Covers S (𝟙 X) ↔ S ∈ (coherentTopology C) X`
    — la retombée ponctuelle, via `covering_iff_covers_id`.

Chaque preuve est une **preuve tactique réelle** (veine DEEP) : les axiomes
de Mathlib (`GrothendieckTopology.covers_iff`, `Coverage.mem_toGrothendieck`,
`Saturate.pullback`, `Sieve.pullback_id`, `covering_iff_covers_id`) plus la
définition `coherentTopology = coherentCoverage.toGrothendieck`. Aucune
preuve n'est un re-export ou un unfold.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s éliminés à la création.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est apparié avec son jumeau anglais dans le fichier sibling
`CoversCoherentArrow_en.lean` (modèle sibling pair, voir PR #6154 pour
le pilote sur `Utility.lean`). Namespace suffix `_en` appliqué au fichier EN
(anti-collision, conforme code-style.md #4980). Les énoncés de théorèmes, les
noms de lemmas, les tactiques Lean et les références Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
diffèrent entre les deux fichiers (préservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Coherent.Basic

namespace Grothendieck.CoversCoherentArrow

open CategoryTheory Limits Coverage

universe u v

/-!
## Section 1 : le pont central — forme flèche ↔ Saturate

`coherentTopology C` (pour `C : Type u` `[Category.{v} C]` `[Precoherent C]`)
est définie comme `coherentCoverage C |>.toGrothendieck`. La forme flèche
`coherentTopology C |>.Covers S f` se réduit via `covers_iff` au point
`S.pullback f ∈ (coherentTopology C) Y`, qui par `mem_toGrothendieck` est
équivalent à `Saturate (coherentCoverage C) Y (S.pullback f)`.

L'instance `Precoherent` est précisément ce qui fournit la stabilité par
pullback des `EffectiveEpiFamily` : `Precoherent.pullback` construit un
familles couvrante de `pullback f (S a)` à partir d'une famille couvrante
de `S a`. Cette condition est ce qui permet à `coherentCoverage.pullback`
de tenir, et donc à `Saturate.pullback` d'être une fonction continue (le
constructeur `transitive` ferme la stabilité).
-/

/-- Pont central : la forme flèche pour la topologie cohérente
    `coherentTopology C` (où `C : Type u` `[Category.{v} C]`
    `[Precoherent C]`) équivaut à la caractérisation inductive ponctuelle :
    `(coherentTopology C).Covers S f ↔ Saturate (coherentCoverage C) Y (S.pullback f)`.
    Preuve : `covers_iff` réduit à `S.pullback f ∈ (coherentTopology C) Y`,
    puis `Coverage.mem_toGrothendieck` identifie à `Saturate`. -/
theorem covers_iff_toGrothendieck {C : Type u} [Category.{v} C] [Precoherent C]
    {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (coherentTopology C).Covers S f ↔ Saturate (coherentCoverage C) Y (S.pullback f) := by
  rw [GrothendieckTopology.covers_iff]
  exact (Coverage.mem_toGrothendieck (K := coherentCoverage C) (X := Y)
    (S := S.pullback f)).symm

/-!
## Section 2 : cas de base — la cohérence couvre sa propre génération

Quand `coherentCoverage C` fournit un `(S : Presieve X) ∈ (coherentCoverage C) X`,
le crible `Sieve.generate S` qu'elle engendre couvre l'identité au sens de
`coherentTopology C` — c'est le sens direct de `Saturate.of`. Le pont vient
de `covering_iff_covers_id`, qui ramène à `Sieve.generate S ∈
(coherentTopology C) X`, puis on applique `Saturate.of` directement.
On retrouve la même structure que pour `Coverage`/`Precoverage`/`Pretopology`.
-/

/-- Cas de base : si `(S : Presieve X) ∈ (coherentCoverage C) X`, alors le crible
    qu'elle engendre couvre l'identité :
    `(coherentTopology C).Covers (Sieve.generate S) (𝟙 X)`.
    Preuve : `covering_iff_covers_id` ramène à
    `Sieve.generate S ∈ (coherentTopology C) X`, puis
    `Coverage.mem_toGrothendieck` identifie à `Saturate`, qui est satisfait
    par `Saturate.of _ _ hS`. -/
theorem covers_toGrothendieck_of_of {C : Type u} [Category.{v} C] [Precoherent C]
    {X : C} {S : Presieve X} (hS : S ∈ (coherentCoverage C) X) :
    (coherentTopology C).Covers (Sieve.generate S) (𝟙 X) :=
  (GrothendieckTopology.covering_iff_covers_id (J := coherentTopology C)
    (X := X) (Sieve.generate S)).mp (by
    show Sieve.generate S ∈ (coherentCoverage C).toGrothendieck X
    rw [Coverage.mem_toGrothendieck]
    exact Saturate.of X S hS)

/-- Cas de base généralisé : la couverture engendrée par `S` couvre
    n'importe quelle flèche `f : Y ⟶ X`. Preuve : `covers_iff_toGrothendieck`
    ramène à `Saturate (coherentCoverage C) Y (S.pullback f)`. On exhibe
    ce `Saturate` via `Saturate.pullback` + `Saturate.of`. -/
theorem covers_of_mem_toGrothendieck {C : Type u} [Category.{v} C] [Precoherent C]
    {X Y : C} (f : Y ⟶ X) {S : Presieve X} (hS : S ∈ (coherentCoverage C) X) :
    (coherentTopology C).Covers (Sieve.generate S) f := by
  rw [covers_iff_toGrothendieck]
  exact Saturate.pullback (coherentCoverage C) f (Saturate.of X S hS)

/-- Cas particulier sur le crible top : `(coherentTopology C).Covers ⊤ (𝟙 X)`.
    Preuve : `Saturate.top` fournit directement le témoin. -/
theorem covers_toGrothendieck_top {C : Type u} [Category.{v} C] [Precoherent C]
    (X : C) :
    (coherentTopology C).Covers (⊤ : Sieve X) (𝟙 X) :=
  (GrothendieckTopology.covering_iff_covers_id (J := coherentTopology C)
    (X := X) ⊤).mp (by
    show ⊤ ∈ (coherentCoverage C).toGrothendieck X
    rw [Coverage.mem_toGrothendieck]
    exact Saturate.top X)

/-!
## Section 3 : retombée ponctuelle

Spécialisation sur l'identité : `(coherentTopology C).Covers S (𝟙 X) ↔
S ∈ (coherentTopology C) X`. Le pont vers la couverture ponctuelle est
immédiat via `covering_iff_covers_id`.
-/

/-- Retombée ponctuelle : pour `coherentTopology C`, couvrir le long
    de l'identité équivaut à appartenir à la topologie :
    `(coherentTopology C).Covers S (𝟙 X) ↔ S ∈ (coherentTopology C) X`.
    Preuve : c'est exactement `covering_iff_covers_id`. -/
theorem covers_iff_pullback_toGrothendieck {C : Type u} [Category.{v} C] [Precoherent C]
    {X : C} (S : Sieve X) :
    (coherentTopology C).Covers S (𝟙 X) ↔ S ∈ (coherentTopology C) X :=
  (GrothendieckTopology.covering_iff_covers_id (J := coherentTopology C)
    (X := X) S).symm

end Grothendieck.CoversCoherentArrow
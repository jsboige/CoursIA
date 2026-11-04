/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 55b : forme flèche de la topologie régulière

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Cette partie applique le fil conducteur « forme flèche » à la **topologie
régulière** (`regularTopology`) sur une catégorie `Preregular`. Mathlib
fournit au niveau ponctuel `mem_toGrothendieck` via `Saturate`, mais
**aucune loi ne la connecte à la forme flèche** `regularTopology.Covers`.
On comble le trou par cinq théorèmes propres — structure identique à
la Partie 55a mais spécialisée à la couverture régulière : la régularité
exige qu'une famille couvrante soit un **morphisme effectif-épimorphe
unique** (`Presieve.singleton h` avec `EffectiveEpi h`, vs famille de
plusimé pour `Coherent`). Cela donne aux théorèmes une saveur
particulière — la couverture « regulière » est mono-flèche, ce qui simplifie
certaines preuves mais exige la condition `Preregular` pour garantir la
stabilité par pullback des morphismes effectifs.

  - `covers_iff_toGrothendieck` (central) : pour
    `regularTopology C` (avec `[Preregular C]`),
    `regularTopology C |>.Covers S f ↔ Saturate (regularCoverage C) Y (S.pullback f)`
    — pont direct entre la forme flèche et la caractérisation inductive
    ponctuelle, via `covers_iff` puis `mem_toGrothendieck`. C'est la
    **loi naturelle** à l'étage régulier.
  - `covers_toGrothendieck_of_of` (cas particulier) : si un morphisme
    `h : X ⟶ B` est effectif-épimorphe, alors le crible singleton
    couvre l'identité : `(regularTopology C).Covers (Sieve.generate
    (Presieve.singleton h)) (𝟙 B)` — la retombée ponctuelle via
    `covering_iff_covers_id`.
  - `covers_toGrothendieck_top` (cas particulier) : la couverture
    triviale `⊤` couvre l'identité : `(regularTopology C).Covers ⊤
    (𝟙 X)`, retombée de `Saturate.top`.
  - `covers_of_mem_toGrothendieck` (cas particulier sur `Sieve.generate`) :
    si un `h : X ⟶ B` est effectif-épimorphe, alors
    `(regularTopology C).Covers (Sieve.generate (Presieve.singleton h)) f`
    pour n'importe quelle `f : Y ⟶ X` — la stabilité par pullback via
    `Saturate.pullback` puis `Saturate.of`.
  - `covers_iff_pullback_toGrothendieck` (cas particulier sur l'identité) :
    `(regularTopology C).Covers S (𝟙 X) ↔ S ∈ (regularTopology C) X`
    — la retombée ponctuelle, via `covering_iff_covers_id`.

Chaque preuve est une **preuve tactique réelle** (veine DEEP) : les axiomes
de Mathlib (`GrothendieckTopology.covers_iff`, `Coverage.mem_toGrothendieck`,
`Saturate.pullback`, `covering_iff_covers_id`) plus la définition
`regularTopology = regularCoverage.toGrothendieck`. Aucune preuve n'est
un re-export ou un unfold.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s éliminés à la création.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est apparié avec son jumeau anglais dans le fichier sibling
`CoversRegularArrow_en.lean` (modèle sibling pair, voir PR #6154 pour
le pilote sur `Utility.lean`). Namespace suffix `_en` appliqué au fichier EN
(anti-collision, conforme code-style.md #4980). Les énoncés de théorèmes, les
noms de lemmas, les tactiques Lean et les références Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
diffèrent entre les deux fichiers (préservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Coherent.Basic

namespace Grothendieck.CoversRegularArrow

open CategoryTheory Limits Coverage

universe u v

/-!
## Section 1 : le pont central — forme flèche ↔ Saturate

`regularTopology C` (pour `C : Type u` `[Category.{v} C]` `[Preregular C]`)
est définie comme `regularCoverage C |>.toGrothendieck`. La forme flèche
`regularTopology C |>.Covers S f` se réduit via `covers_iff` au point
`S.pullback f ∈ (regularTopology C) Y`, qui par `mem_toGrothendieck` est
équivalent à `Saturate (regularCoverage C) Y (S.pullback f)`.

L'instance `Preregular` est précisément ce qui fournit la stabilité par
pullback des morphismes effectifs : `Preregular.exists_fac` construit un
morphisme effectif-épimorphe `h : W ⟶ X` tel que `i ≫ g = h ≫ f`. Cette
condition est ce qui permet à `regularCoverage.pullback` de tenir, et
donc à `Saturate.pullback` d'être une fonction continue.
-/

/-- Pont central : la forme flèche pour la topologie régulière
    `regularTopology C` (où `C : Type u` `[Category.{v} C]`
    `[Preregular C]`) équivaut à la caractérisation inductive ponctuelle :
    `(regularTopology C).Covers S f ↔ Saturate (regularCoverage C) Y (S.pullback f)`.
    Preuve : `covers_iff` réduit à `S.pullback f ∈ (regularTopology C) Y`,
    puis `Coverage.mem_toGrothendieck` identifie à `Saturate`. -/
theorem covers_iff_toGrothendieck {C : Type u} [Category.{v} C] [Preregular C]
    {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (regularTopology C).Covers S f ↔ Saturate (regularCoverage C) Y (S.pullback f) := by
  rw [GrothendieckTopology.covers_iff]
  exact (Coverage.mem_toGrothendieck (K := regularCoverage C) (X := Y)
    (S := S.pullback f)).symm

/-!
## Section 2 : cas de base — la régularité couvre sa propre génération

Quand `regularCoverage C` fournit un morphisme effectif-épimorphe `h : X ⟶ B`,
le crible singleton `Sieve.generate (Presieve.singleton h)` couvre
l'identité au sens de `regularTopology C` — c'est le sens direct de
`Saturate.of`. Le pont vient de `covering_iff_covers_id`, qui ramène à
`Sieve.generate (Presieve.singleton h) ∈ (regularTopology C) B`, puis on
applique `Saturate.of` directement.
-/

/-- Cas de base : si un morphisme `h : X ⟶ B` est effectif-épimorphe
    (`EffectiveEpi h`), alors le crible singleton qu'il engendre couvre
    l'identité :
    `(regularTopology C).Covers (Sieve.generate (Presieve.singleton h)) (𝟙 B)`.
    Preuve : `covering_iff_covers_id` ramène à
    `Sieve.generate (Presieve.singleton h) ∈ (regularTopology C) B`, puis
    `Coverage.mem_toGrothendieck` identifie à `Saturate`, qui est satisfait
    par `Saturate.of _ _ ⟨X, h, rfl, h_eff⟩`. -/
theorem covers_toGrothendieck_of_of {C : Type u} [Category.{v} C] [Preregular C]
    {B : C} {X : C} (h : X ⟶ B) [EffectiveEpi h] :
    (regularTopology C).Covers
      (Sieve.generate (Presieve.singleton h)) (𝟙 B) :=
  (GrothendieckTopology.covering_iff_covers_id (J := regularTopology C)
    (X := B) (Sieve.generate (Presieve.singleton h))).mp (by
    show Sieve.generate (Presieve.singleton h) ∈ (regularCoverage C).toGrothendieck B
    rw [Coverage.mem_toGrothendieck]
    refine Saturate.of B (Presieve.singleton h)
      ⟨X, h, (Presieve.ofArrows_pUnit h).symm, ?_⟩
    exact (inferInstance : EffectiveEpi h))

/-- Cas de base généralisé : le crible singleton engendré par `h` couvre
    n'importe quelle flèche `f : Y ⟶ B`. Preuve : `covers_iff_toGrothendieck`
    ramène à `Saturate (regularCoverage C) Y (Sieve.generate (Presieve.singleton h) |>.pullback f)`.
    On exhibe ce `Saturate` via `Saturate.pullback` + `Saturate.of`. -/
theorem covers_of_mem_toGrothendieck {C : Type u} [Category.{v} C] [Preregular C]
    {B : C} {X : C} (h : X ⟶ B) [EffectiveEpi h] {Y : C} (f : Y ⟶ B) :
    (regularTopology C).Covers
      (Sieve.generate (Presieve.singleton h)) f := by
  rw [covers_iff_toGrothendieck]
  exact Saturate.pullback (regularCoverage C) f
    (Saturate.of B (Presieve.singleton h)
      ⟨X, h, (Presieve.ofArrows_pUnit h).symm, (inferInstance : EffectiveEpi h)⟩)

/-- Cas particulier sur le crible top : `(regularTopology C).Covers ⊤ (𝟙 X)`.
    Preuve : `Saturate.top` fournit directement le témoin. -/
theorem covers_toGrothendieck_top {C : Type u} [Category.{v} C] [Preregular C]
    (X : C) :
    (regularTopology C).Covers (⊤ : Sieve X) (𝟙 X) :=
  (GrothendieckTopology.covering_iff_covers_id (J := regularTopology C)
    (X := X) ⊤).mp (by
    show ⊤ ∈ (regularCoverage C).toGrothendieck X
    rw [Coverage.mem_toGrothendieck]
    exact Saturate.top X)

/-!
## Section 3 : retombée ponctuelle

Spécialisation sur l'identité : `(regularTopology C).Covers S (𝟙 X) ↔
S ∈ (regularTopology C) X`. Le pont vers la couverture ponctuelle est
immédiat via `covering_iff_covers_id`.
-/

/-- Retombée ponctuelle : pour `regularTopology C`, couvrir le long
    de l'identité équivaut à appartenir à la topologie :
    `(regularTopology C).Covers S (𝟙 X) ↔ S ∈ (regularTopology C) X`.
    Preuve : c'est exactement `covering_iff_covers_id`. -/
theorem covers_iff_pullback_toGrothendieck {C : Type u} [Category.{v} C] [Preregular C]
    {X : C} (S : Sieve X) :
    (regularTopology C).Covers S (𝟙 X) ↔ S ∈ (regularTopology C) X :=
  (GrothendieckTopology.covering_iff_covers_id (J := regularTopology C)
    (X := X) S).symm

end Grothendieck.CoversRegularArrow
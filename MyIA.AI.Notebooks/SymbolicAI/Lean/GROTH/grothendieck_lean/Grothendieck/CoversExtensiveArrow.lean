/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 55c : forme flèche de la topologie extensive

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Cette partie applique le fil conducteur « forme flèche » à la **topologie
extensive** (`extensiveTopology`) sur une catégorie `FinitaryPreExtensive`.
Mathlib fournit au niveau ponctuel `mem_toGrothendieck` via `Saturate`,
mais **aucune loi ne la connecte à la forme flèche**
`extensiveTopology.Covers`. On comble le trou par cinq théorèmes propres —
structure identical aux à la Partie 55a mais spécialisée à la couverture
extensive : l'extensivité exige qu'une famille couvrante soit une famille
**finie** `Presieve.ofArrows X π` dont le `Sigma.desc π` est un isomorphisme.
Cela donne aux théorèmes une saveur particulière — la couverture extensive
est la caractérisation combinatoire des sommes disjointes (coproduits
stricts).

  - `covers_iff_toGrothendieck` (central) : pour
    `extensiveTopology C` (avec `[FinitaryPreExtensive C]`),
    `extensiveTopology C |>.Covers S f ↔ Saturate (extensiveCoverage C) Y (S.pullback f)`
    — pont direct entre la forme flèche et la caractérisation inductive
    ponctuelle, via `covers_iff` puis `mem_toGrothendieck`. C'est la
    **loi naturelle** à l'étage extensif.
  - `covers_toGrothendieck_of_of` (cas particulier) : si une famille
    `X : α → C`, `π : (a : α) → (X a ⟶ B)` avec `α` fini et
    `IsIso (Sigma.desc π)`, alors le crible `Sieve.generate
    (Presieve.ofArrows X π)` couvre l'identité :
    `(extensiveTopology C).Covers (Sieve.generate (Presieve.ofArrows X π)) (𝟙 B)`
    — la retombée ponctuelle via `covering_iff_covers_id`.
  - `covers_toGrothendieck_top` (cas particulier) : la couverture
    triviale `⊤` couvre l'identité : `(extensiveTopology C).Covers ⊤
    (𝟙 X)`, retombée de `Saturate.top`.
  - `covers_of_mem_toGrothendieck` (cas particulier sur `Sieve.generate`) :
    si une famille `X : α → C`, `π : (a : α) → (X a ⟶ B)` avec `α` fini
    et `IsIso (Sigma.desc π)`, alors
    `(extensiveTopology C).Covers (Sieve.generate (Presieve.ofArrows X π)) f`
    pour n'importe quelle `f : Y ⟶ B` — la stabilité par pullback via
    `Saturate.pullback` puis `Saturate.of`.
  - `covers_iff_pullback_toGrothendieck` (cas particulier sur l'identité) :
    `(extensiveTopology C).Covers S (𝟙 X) ↔ S ∈ (extensiveTopology C) X`
    — la retombée ponctuelle, via `covering_iff_covers_id`.

Chaque preuve est une **preuve tactique réelle** (veine DEEP) : les axiomes
de Mathlib (`GrothendieckTopology.covers_iff`, `Coverage.mem_toGrothendieck`,
`Saturate.pullback`, `covering_iff_covers_id`) plus la définition
`extensiveTopology = extensiveCoverage.toGrothendieck`. Aucune preuve n'est
un re-export ou un unfold.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s éliminés à la création.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est apparié avec son jumeau anglais dans le fichier sibling
`CoversExtensiveArrow_en.lean` (modèle sibling pair, voir PR #6154 pour
le pilote sur `Utility.lean`). Namespace suffix `_en` appliqué au fichier EN
(anti-collision, conforme code-style.md #4980). Les énoncés de théorèmes, les
noms de lemmas, les tactiques Lean et les références Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
diffèrent entre les deux fichiers (préservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Coherent.Basic

namespace Grothendieck.CoversExtensiveArrow

open CategoryTheory Limits Coverage

universe u v

/-!
## Section 1 : le pont central — forme flèche ↔ Saturate

`extensiveTopology C` (pour `C : Type u` `[Category.{v} C]`
`[FinitaryPreExtensive C]`) est définie comme
`extensiveCoverage C |>.toGrothendieck`. La forme flèche
`extensiveTopology C |>.Covers S f` se réduit via `covers_iff` au point
`S.pullback f ∈ (extensiveTopology C) Y`, qui par `mem_toGrothendieck` est
équivalent à `Saturate (extensiveCoverage C) Y (S.pullback f)`.

L'instance `FinitaryPreExtensive` est précisément ce qui fournit la
stabilité par pullback des sommes disjointes finies :
`FinitaryPreExtensive.isIso_sigmaDesc_fst` reconstruit un isomorphisme de
`Sigma.desc (fun x => pullback.fst (π x) f)` à partir d'un isomorphisme
de `Sigma.desc π`. Cette condition est ce qui permet à
`extensiveCoverage.pullback` de tenir, et donc à `Saturate.pullback`
d'être une fonction continue.
-/

/-- Pont central : la forme flèche pour la topologie extensive
    `extensiveTopology C` (où `C : Type u` `[Category.{v} C]`
    `[FinitaryPreExtensive C]`) équivaut à la caractérisation inductive
    ponctuelle :
    `(extensiveTopology C).Covers S f ↔ Saturate (extensiveCoverage C) Y (S.pullback f)`.
    Preuve : `covers_iff` réduit à `S.pullback f ∈ (extensiveTopology C) Y`,
    puis `Coverage.mem_toGrothendieck` identifie à `Saturate`. -/
theorem covers_iff_toGrothendieck {C : Type u} [Category.{v} C] [FinitaryPreExtensive C]
    {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (extensiveTopology C).Covers S f ↔ Saturate (extensiveCoverage C) Y (S.pullback f) := by
  rw [GrothendieckTopology.covers_iff]
  exact (Coverage.mem_toGrothendieck (K := extensiveCoverage C) (X := Y)
    (S := S.pullback f)).symm

/-!
## Section 2 : cas de base — l'extensivité couvre sa propre génération

Quand `extensiveCoverage C` fournit une famille finie `X : α → C`,
`π : (a : α) → (X a ⟶ B)` avec `IsIso (Sigma.desc π)`, le crible
`Sieve.generate (Presieve.ofArrows X π)` couvre l'identité au sens de
`extensiveTopology C` — c'est le sens direct de `Saturate.of`. Le pont
vient de `covering_iff_covers_id`, qui ramène à
`Sieve.generate (Presieve.ofArrows X π) ∈ (extensiveTopology C) B`,
puis on applique `Saturate.of` directement.
-/

/-- Cas de base : si une famille finie `X : α → C`, `π : (a : α) → (X a ⟶ B)`
    a un `Sigma.desc π` qui est un isomorphisme, alors le crible qu'elle
    engendre couvre l'identité :
    `(extensiveTopology C).Covers (Sieve.generate (Presieve.ofArrows X π)) (𝟙 B)`.
    Preuve : `covering_iff_covers_id` ramène à
    `Sieve.generate (Presieve.ofArrows X π) ∈ (extensiveTopology C) B`,
    puis `Coverage.mem_toGrothendieck` identifie à `Saturate`, qui est
    satisfait par `Saturate.of _ _ ⟨α, hα, X, π, rfl, h_iso⟩`. -/
theorem covers_toGrothendieck_of_of {C : Type u} [Category.{v} C] [FinitaryPreExtensive C]
    {B : C} {α : Type} [Finite α] (X : α → C) (π : (a : α) → (X a ⟶ B))
    (h_iso : IsIso (Sigma.desc π)) :
    (extensiveTopology C).Covers
      (Sieve.generate (Presieve.ofArrows X π)) (𝟙 B) :=
  (GrothendieckTopology.covering_iff_covers_id (J := extensiveTopology C)
    (X := B) (Sieve.generate (Presieve.ofArrows X π))).mp (by
    show Sieve.generate (Presieve.ofArrows X π) ∈ (extensiveCoverage C).toGrothendieck B
    rw [Coverage.mem_toGrothendieck]
    exact Saturate.of B (Presieve.ofArrows X π) ⟨α, inferInstance, X, π, rfl, h_iso⟩)

/-- Cas de base généralisé : le crible engendré par la famille `X, π`
    couvre n'importe quelle flèche `f : Y ⟶ B`. Preuve :
    `covers_iff_toGrothendieck` ramène à
    `Saturate (extensiveCoverage C) Y (Sieve.generate (Presieve.ofArrows X π) |>.pullback f)`.
    On exhibe ce `Saturate` via `Saturate.pullback` + `Saturate.of`. -/
theorem covers_of_mem_toGrothendieck {C : Type u} [Category.{v} C] [FinitaryPreExtensive C]
    {B : C} {α : Type} [Finite α] (X : α → C) (π : (a : α) → (X a ⟶ B))
    (h_iso : IsIso (Sigma.desc π)) {Y : C} (f : Y ⟶ B) :
    (extensiveTopology C).Covers
      (Sieve.generate (Presieve.ofArrows X π)) f := by
  rw [covers_iff_toGrothendieck]
  exact Saturate.pullback (extensiveCoverage C) f
    (Saturate.of B (Presieve.ofArrows X π) ⟨α, inferInstance, X, π, rfl, h_iso⟩)

/-- Cas particulier sur le crible top : `(extensiveTopology C).Covers ⊤ (𝟙 X)`.
    Preuve : `Saturate.top` fournit directement le témoin. -/
theorem covers_toGrothendieck_top {C : Type u} [Category.{v} C] [FinitaryPreExtensive C]
    (X : C) :
    (extensiveTopology C).Covers (⊤ : Sieve X) (𝟙 X) :=
  (GrothendieckTopology.covering_iff_covers_id (J := extensiveTopology C)
    (X := X) ⊤).mp (by
    show ⊤ ∈ (extensiveCoverage C).toGrothendieck X
    rw [Coverage.mem_toGrothendieck]
    exact Saturate.top X)

/-!
## Section 3 : retombée ponctuelle

Spécialisation sur l'identité : `(extensiveTopology C).Covers S (𝟙 X) ↔
S ∈ (extensiveTopology C) X`. Le pont vers la couverture ponctuelle est
immédiat via `covering_iff_covers_id`.
-/

/-- Retombée ponctuelle : pour `extensiveTopology C`, couvrir le long
    de l'identité équivaut à appartenir à la topologie :
    `(extensiveTopology C).Covers S (𝟙 X) ↔ S ∈ (extensiveTopology C) X`.
    Preuve : c'est exactement `covering_iff_covers_id`. -/
theorem covers_iff_pullback_toGrothendieck {C : Type u} [Category.{v} C] [FinitaryPreExtensive C]
    {X : C} (S : Sieve X) :
    (extensiveTopology C).Covers S (𝟙 X) ↔ S ∈ (extensiveTopology C) X :=
  (GrothendieckTopology.covering_iff_covers_id (J := extensiveTopology C)
    (X := X) S).symm

end Grothendieck.CoversExtensiveArrow
/-
  vihdzp/combinatorial-games Reference Project
  =============================================

  This project references vihdzp/combinatorial-games as a Lake dependency
  to explore and present their formalized combinatorial game theory results:

  - Surreal numbers (field structure, dyadic representation, Hahn series)
  - Nimbers (algebraically closed field of characteristic 2)
  - General combinatorial games (birthday, canonical form, impartial games)
  - Sign expansions and ordinal representations

  This is the upstream repository that superseded Mathlib's CGT modules,
  removed in PR #35550 (Feb 2026) after 6 months of deprecation (PR #28063).

  Reference: https://github.com/vihdzp/combinatorial-games
  Authors: Violeta Hernandez Palacios (vihdzp)
  License: Apache-2.0
-/

import Lake
open Lake DSL

package «conway_cgt» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require CombinatorialGames from git
  "https://github.com/vihdzp/combinatorial-games.git"

@[default_target]
lean_lib «CGTTour» where
  -- Tour of vihdzp/combinatorial-games results
  -- Convention i18n #4980: globs build FR root + EN sibling (drift-CI gate).
  -- NOTE technique (po-2026 fix du glob cassé, cf decision_theory_lean lakefile) :
  -- `CGTTour.lean` est un module FEUILLE (pas de sous-dossier `CGTTour/`).
  -- Le glob `CGTTour.*` (= Glob.submodules) cherche `CGTTour` comme un
  -- répertoire pour énumérer ses enfants -> erreur lake
  -- `no such file ... CGTTour` (CI #6116 RED ; reproduit in vitro sur projet
  -- lake minimal). Sur un root feuille il faut des noms bare explicites pour
  -- chaque module top-level : `CGTTour` (FR canonique) + `CGTTour_en` (sibling).
  -- Vérifié in vitro : `globs := #[`Foo, `Foo_en]` compile les deux .olean.
  -- Pattern bare-names éprouvé : cooperative_games_lean/lakefile.lean.
  globs := #[`CGTTour, `CGTTour_en]

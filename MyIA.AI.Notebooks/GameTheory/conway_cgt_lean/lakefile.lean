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

-- CGTTour.lean imports ONLY `CombinatorialGames.*` modules (no direct
-- `import Mathlib.*`), so mathlib is not required directly here: it arrives
-- transitively through CombinatorialGames with that project's own coherent pin
-- set (mathlib 5eec30bc, batteries d60e644, aesop 57d3325, plausible b1c4a69).
-- Declaring `require mathlib` directly and unpinned made Lake resolve two
-- DISAGREEING pin sets for batteries/aesop/plausible — the root cause of the
-- build failure. It was never a `require` ordering problem (why the reorder-only
-- attempt #6432 failed). CombinatorialGames is pinned to a reproducible master
-- SHA; its lean-toolchain (v4.33.0-rc1) is matched by our lean-toolchain so the
-- mathlib olean cache (`lake exe cache get`) hits. See #6116.
--
-- Migration 4.33 (#14773 Phase 5, 2026-09-28) : l'amont n'a JAMAIS épinglé
-- `v4.33.0` final (historique `lean-toolchain` de vihdzp/combinatorial-games :
-- v4.33.0-rc1 le 2026-07-29, puis v4.34.0-rc2 le 2026-09-07). La révision
-- retenue est donc la dernière de la fenêtre 4.33 (`bb863d3deb77`, 2026-09-07),
-- dont la paire (toolchain rc1, mathlib 5eec30bc) est cohérente et servie par
-- le cache oleans. Forcer `v4.33.0` final contre un mathlib rc1 serait le
-- version-skate que la Phase 5 interdit.
require CombinatorialGames from git
  "https://github.com/vihdzp/combinatorial-games.git" @ "bb863d3deb779f709920996cf5ab674d8655083b"

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

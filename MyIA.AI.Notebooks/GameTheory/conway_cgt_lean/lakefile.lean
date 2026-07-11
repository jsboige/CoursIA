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
  -- Convention i18n #4980: globs for sibling CGTTour_en.lean auto-discovery
  -- NOTE technique (cf RepeatedGames lakefile precedent, PR #5360, c.218) :
  -- `Foo.*` est un glob de sous-modules (matche `Foo` + `Foo.X`).
  -- `CGTTour_en.lean` est un module top-level sibling (PAS un sous-module
  -- de `CGTTour`) -> il faut le nommer explicitement pour que `lake build`
  -- le compile et que la protection drift-CI s'applique (exigence (b)).
  globs := #[`CGTTour.*, `CGTTour_en]

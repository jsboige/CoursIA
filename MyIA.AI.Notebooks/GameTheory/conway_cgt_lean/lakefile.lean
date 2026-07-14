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

-- require order: CombinatorialGames first, mathlib LAST.
-- Reason (cf issue #6419): Lake resolves transitive pins in declaration
-- order; the LAST `require` wins for shared deps (Batteries / Aesop /
-- Plausible). With mathlib first, CombinatorialGames transitively pinned
-- older versions that mismatched what mathlib resolves -> `mathlib:
-- failed to fetch cache` + build failures on Batteries.Data.Nat.Basic,
-- Plausible.Testable, Aesop.Builder.Forward. Reordering so mathlib is
-- last lets Mathlib's versions win and resolves the mismatch.
require CombinatorialGames from git
  "https://github.com/vihdzp/combinatorial-games.git"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «CGTTour» where
  -- Tour of vihdzp/combinatorial-games results

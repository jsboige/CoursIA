import Lake
open Lake DSL

package «knot_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

-- shua/leanknot (Lean 4 branch) — bricks/walls, Reidemeister, tangles, links, braids
-- Repository: https://github.com/shua/leanknot
-- Reference: Prathamesh (2015), Formalising Knot Theory in Isabelle/HOL
-- Note: not yet added as Lake dependency — requires Lean 4 toolchain alignment
-- with our lean-toolchain. Will be integrated once toolchain versions match.

@[default_target]
lean_lib «Knots» where
  -- `.submodules `Knots` covers the Knots.* submodules (FR + their _en siblings);
  -- the root `Knots_en` aggregator must be globbed explicitly (bare `.submodules`
  -- matches only submodules, not sibling root modules), pattern #6585 / #4980.
  globs := #[.submodules `Knots, `Knots_en]

import Lake
open Lake DSL

package «knot_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

-- shua/leanknot (Lean 4 branch) — bricks/walls, Reidemeister, tangles, links, braids
-- Repository: https://github.com/shua/leanknot
-- Reference: Prathamesh (2015), Formalising Knot Theory in Isabelle/HOL
-- Note: not yet added as Lake dependency — requires Lean 4 toolchain alignment
-- with our lean-toolchain. Will be integrated once toolchain versions match.

@[default_target]
lean_lib «Knots» where
  -- `.andSubmodules `Knots` covers the FR root aggregator `Knots.lean` itself plus
  -- the Knots.* submodules (FR + their _en siblings); the root `Knots_en` aggregator
  -- must still be globbed explicitly (a glob entry matches one root module only),
  -- pattern #6585 / #4980. FR root glob added when wiring ReidemeisterCombinatorial
  -- into it: with `.submodules` alone, `lake build` never elaborated `Knots.lean`.
  globs := #[.andSubmodules `Knots, `Knots_en]

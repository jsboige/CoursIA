/-
  DominikPeters/SocialChoiceLean Reference Project
  =================================================

  This project references DominikPeters/SocialChoiceLean as a Lake dependency
  to explore and present their formalized social choice results:

  - Gibbard-Satterthwaite theorem
  - Condorcet impossibilities (participation, reinforcement, strategyproofness)
  - Duggan-Schwartz theorem
  - Holliday's impossibility
  - 15+ voting rules with axiom verification (Split Cycle, Schulze, Black, etc.)

  Reference: https://github.com/DominikPeters/SocialChoiceLean
  License: MIT (DominikPeters)
-/

import Lake
open Lake DSL

package «social_choice_peters» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "8cb9319191fd34b6f23d7ffea58a4f8fb674cefd"

require SocialChoiceLean from git
  "https://github.com/DominikPeters/SocialChoiceLean.git"

@[default_target]
lean_lib «PetersTour» where
  -- Tour of DominikPeters/SocialChoiceLean results
  -- globs incluent le sibling EN (i18n #4980) pour que `lake build` le compile
  -- aussi : sans cela, PetersTour_en.lean n'est jamais élaboré et un Lean CI
  -- vert est un faux pass (orphan-trap #6749). Même pattern que sudoku_lean.
  globs := #[`PetersTour, `PetersTour_en]

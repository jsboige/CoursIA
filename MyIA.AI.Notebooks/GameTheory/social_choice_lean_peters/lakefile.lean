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

require SocialChoiceLean from git
  "https://github.com/DominikPeters/SocialChoiceLean.git"

@[default_target]
lean_lib «PetersTour» where
  -- Tour of DominikPeters/SocialChoiceLean results

import Lake
open Lake DSL

package «social_choice» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «SocialChoice» where
  -- Port of asouther4/lean-social-choice to Lean 4
  -- Arrow's Impossibility Theorem and Sen's Theorem

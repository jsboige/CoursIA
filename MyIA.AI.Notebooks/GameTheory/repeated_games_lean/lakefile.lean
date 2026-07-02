import Lake
open Lake DSL

package «repeated_games» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «RepeatedGames» where
  -- Repeated Games Library for Lean 4
  -- Includes: stage game (Prisoner's Dilemma), discounting, grim trigger
  -- Theorem phare: grim_trigger_sustains_iff (one-shot deviation principle)

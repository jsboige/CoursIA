import Lake
open Lake DSL

package «stable_marriage» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «StableMarriage» where
  -- Gale-Shapley Stable Marriage Theorem formalization

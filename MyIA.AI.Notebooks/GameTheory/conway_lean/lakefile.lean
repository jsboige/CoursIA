import Lake
open Lake DSL

package «conway» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Conway» where
  -- Conway hommage: accessible formalizations of lesser-known results
  -- by John Horton Conway (1937-2020)

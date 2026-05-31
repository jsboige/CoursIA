import Lake
open Lake DSL

package «grothendieck» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Grothendieck» where
  -- Grothendieck tribute: Mathlib tour of Grothendieck's mathematical language
  -- Alexandre Grothendieck (1928-2014).
  -- Categories, sites, sheaves, schemes, Zariski topology — as they live in Mathlib 4.

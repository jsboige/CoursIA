import Lake
open Lake DSL

package «sensitivity» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Sensitivity» where
  -- Dust-off of mathlib4/Archive/Sensitivity.lean (Huang 2019 degree theorem)
  -- Original authors: Reid Barton, Johan Commelin, Jesse Michael Han,
  --   Chris Hughes, Robert Y. Lewis, Patrick Massot
  -- Apache 2.0 license preserved
  -- `.submodules `Sensitivity` covers the Sensitivity.* submodules (FR + their _en siblings);
  -- the root `Sensitivity_en` aggregator must be globbed explicitly (bare `.submodules`
  -- matches only submodules, not sibling root modules), pattern #6585 / #4980.
  globs := #[.submodules `Sensitivity, `Sensitivity_en]

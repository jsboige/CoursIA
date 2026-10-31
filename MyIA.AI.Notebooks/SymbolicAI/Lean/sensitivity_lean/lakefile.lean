import Lake
open Lake DSL

package «sensitivity» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib «Sensitivity» where
  -- Dust-off of mathlib4/Archive/Sensitivity.lean (Huang 2019 degree theorem)
  -- Original authors: Reid Barton, Johan Commelin, Jesse Michael Han,
  --   Chris Hughes, Robert Y. Lewis, Patrick Massot
  -- Apache 2.0 license preserved
  -- `.submodules `Sensitivity` covers the Sensitivity.* submodules (FR + their _en siblings);
  -- the two root aggregators `Sensitivity` and `Sensitivity_en` must be globbed explicitly
  -- (bare `.submodules` matches only submodules, not root modules — the library name does
  -- not add its own root either), pattern #6585 / #4980.
  -- Measured: without `Sensitivity` here, `lake build` reports success over 3025 jobs and
  -- never writes `.lake/build/lib/lean/Sensitivity.olean`, so `import Sensitivity` in a
  -- notebook resolves to nothing and only `open Sensitivity` fails ("unknown namespace").
  globs := #[.submodules `Sensitivity, `Sensitivity, `Sensitivity_en]

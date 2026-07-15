import Lake
open Lake DSL

package «calibration» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Calibration» where
  -- `.submodules `Calibration` covers the Calibration.* submodules (FR + their _en siblings);
  -- the root `Calibration_en` aggregator must be globbed explicitly (bare `.submodules`
  -- matches only submodules, not sibling root modules), pattern #6585 / #4980.
  globs := #[.submodules `Calibration, `Calibration_en]
  -- Calibration targets for multi-agent Lean prover (Epic #1452).
  -- Each theorem is a self-contained proof challenge designed to exercise
  -- specific harness paths (P1/P2/P3 from Epic #1453).

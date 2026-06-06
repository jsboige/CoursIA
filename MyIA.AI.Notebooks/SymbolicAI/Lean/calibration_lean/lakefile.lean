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
  -- Calibration targets for multi-agent Lean prover (Epic #1452).
  -- Each theorem is a self-contained proof challenge designed to exercise
  -- specific harness paths (P1/P2/P3 from Epic #1453).

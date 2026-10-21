import Lake
open Lake DSL

package «riemann200» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib «Riemann200» where
  -- Premier module Lean de la série Riemann200 (critère 2 de l'EPIC #20403).
  -- Même pin Mathlib que serre100_lean / hecke_lean (v4.33.0 / db584cd6d46c) :
  -- les `.submodules` couvrent les modules FR ; l'agrégateur racine
  -- `Riemann200` est FR-only by design (rollout i18n DRAINED, pattern #4980).
  globs := #[.submodules `Riemann200, `Riemann200]

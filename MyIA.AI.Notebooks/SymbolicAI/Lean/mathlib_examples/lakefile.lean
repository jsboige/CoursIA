import Lake
open Lake DSL

package «mathlib_examples» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MathLibExamples» where
  -- Convention i18n #4980: globs build FR root + EN sibling (orphan-trap guard).
  -- Without an explicit `globs`, Lake roots the lib at `MathLibExamples.lean`
  -- only, so `Basic_en.lean` is never compiled (the FR root imports `Basic`,
  -- not `Basic_en`). Verified by `scripts/lean/check_i18n_siblings.py --all`
  -- post-#6774. Pattern: sudoku_lean, minimax_lean, learning_theory_lean.
  globs := #[.submodules `MathLibExamples] -- includes Basic + Basic_en

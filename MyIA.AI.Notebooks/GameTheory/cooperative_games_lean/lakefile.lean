import Lake
open Lake DSL

package «cooperative_games» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «CooperativeGames» where
  -- Cooperative Game Theory Library for Lean 4
  -- Includes: TU games, Shapley value, Core, Voting games
  --
  -- i18n FR-first (EPIC #4980 ratif 2026-07-04 11:58Z, comment-4881909354) :
  -- `globs := #[.submodules \`CooperativeGames]` force Lake à compiler
  -- AUSSI les fichiers `_en.lean` siblings (ex : `Basic_en.lean`,
  -- `ConeKernel_en.lean`). Sans cette clause, Lake ne descend pas dans
  -- les `.lean` non-importés — les `_en` seraient livrés orphelins
  -- non-compilés (faux positif STRUCTURAL_ONLY H.4).
  globs := #[.submodules `CooperativeGames]

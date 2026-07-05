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
  -- Globs precis ciblant UNIQUEMENT les fichiers de cette tranche :
  -- `ConeKernel.lean` (FR canonique) + `ConeKernel_en.lean` (EN sibling
  -- verbatim). Pattern precis plutot que `.submodules \`CooperativeGames`
  -- car un autre _en pre-existant sur main (`Basic_en.lean`, ajoute par
  -- PR #5344 commit 24a2da95f) a un bug de namespace resolution
  -- (`G.Convex` non-prefixe dans `namespace MarginalVector`, fail
  -- `open TUGame` manquant) — le `.submodules` l'aurait active en
  -- doublon de la presente PR. Le pattern precis compile SEUL les
  -- fichiers de la tranche, sans toucher les autres _en pre-existants.
  globs := #[`CooperativeGames.ConeKernel, `CooperativeGames.ConeKernel_en]

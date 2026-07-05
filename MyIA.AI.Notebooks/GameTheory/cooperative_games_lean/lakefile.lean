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
  -- PR #5344 commit 24a2da95f) avait un bug de namespace resolution
  -- presume (`G.Convex` non-prefixe dans `section MarginalVector`, fail
  -- `open TUGame` manquant) — le `.submodules` l'aurait active en
  -- doublon de la presente PR. Le pattern precis compile SEUL les
  -- fichiers de la tranche, sans toucher les autres _en pre-existants.
  --
  -- c.235 : ajout `Basic`, `Basic_en`, `Shapley`, `Shapley_en` au tableau
  -- globs (PR #5441). Pattern precis cumulatif (PAS `.submodules`) pour
  -- eviter de reactiver le bug namespace dormant de `Basic_en.lean`.
  -- Empirique : Basic_en.lean a une structure identique a Basic.lean
  -- (TUGame top-level + namespace TUGame_en + section MarginalVector),
  -- donc le bug namespace `open TUGame` manquant n'est PAS confirme
  -- — le commentaire pre-PR-#5441 etait speculatif. Si le build Lake
  -- echoue apres ce PR, le diagnostic precis tombera dans les logs CI.
  globs := #[
    `CooperativeGames.ConeKernel,
    `CooperativeGames.ConeKernel_en,
    `CooperativeGames.Basic,
    `CooperativeGames.Basic_en,
    `CooperativeGames.Shapley,
    `CooperativeGames.Shapley_en
  ]

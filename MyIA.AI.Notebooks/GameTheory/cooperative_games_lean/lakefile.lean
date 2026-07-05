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
  -- Globs precis par tranche (FR canonique + EN sibling verbatim),
  -- etendu incrementalement au fur et a mesure que les _en siblings
  -- sont livres (cycle c.234 : ajout de `Shapley`+`Shapley_en` post-#5419).
  -- Pattern precis plutot que `.submodules \`CooperativeGames`
  -- car un autre _en pre-existant sur main (`Basic_en.lean`, ajoute par
  -- PR #5344 commit 24a2da95f) a un bug de namespace resolution
  -- (`G.Convex` non-prefixe dans `namespace MarginalVector`, fail
  -- `open TUGame` manquant) — le `.submodules` l'aurait active en
  -- doublon des presentes PRs. Le pattern precis compile SEUL les
  -- fichiers des tranches livrees, sans toucher les autres _en pre-existants.
  globs := #[
    `CooperativeGames.ConeKernel, `CooperativeGames.ConeKernel_en,
    `CooperativeGames.Shapley, `CooperativeGames.Shapley_en
  ]

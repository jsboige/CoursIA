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
  -- Globs precis par tranche livree (FR canonique + EN sibling). Le namespace
  -- bug dormant de `Basic_en.lean` (PR #5344 commit 24a2da95f : `structure TUGame`
  -- global mais defs dans `namespace TUGame_en` -> dot-notation `G.Core` cassée)
  -- est desormais FIXE (rename `structure TUGame` -> `structure TUGame_en`,
  -- miroir exact du FR), donc `Basic_en` rejoint les globs.
  -- `Shapley`/`Shapley_en` restent EXCLUS : `Shapley_en.lean` (2035L) a des bugs
  -- residuels (`sorry` + `introN failed` + refs `TUGame` a migrer vers `TUGame_en`)
  -- au-dela du namespace — PR dediee separee requise (fix path #5441 comment).
  -- Pattern precis plutot que `.submodules \`CooperativeGames` pour ne pas
  -- activer `Shapley_en` broken en doublon.
  globs := #[`CooperativeGames.Basic_en, `CooperativeGames.ConeKernel, `CooperativeGames.ConeKernel_en]

import Lake
open Lake DSL

package «game_theory_lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

-- EPIC #4365 — anti-proliferation GameTheory (6->2) : cible « game_theory_lean »
-- regroupera `social_choice` + `cooperative_games` + `stable_marriage` +
-- `social_choice_lean_peters` en un seul lake multi-module, modele `decision_theory_lean`.
--
-- Skeleton c.299 (po-2026) : structure lake validee SANS deplacer aucun
-- module. Les absorptions de modules suivront en PR dediees (c.300+).
--
-- c.306 (po-2026) : ajout d'un second `lean_lib CooperativeGames` qui suit
-- le pattern `decision_theory_lean` (cf `Probas/decision_theory_lean/lakefile.lean`
-- ou `Gittins`/`Utility`/`Coherence` cohabitent comme libs distinctes du
-- meme package `decision_theory_lean`). Cela valide la structure multi-lib
-- du lake cible sans coupler `StableMarriage` et `CooperativeGames`
-- (chaque lib reste un point d'entree independant vers Mathlib).
--
-- Convention i18n EPIC #4980 (cf decision_theory_lean precedent) :
-- `globs` (et non `roots`) avec suffixe `.*` pour auto-decouvrir siblings `_en`.
@[default_target]
lean_lib StableMarriage where
  globs := #[`StableMarriage.*]

@[default_target]
lean_lib CooperativeGames where
  globs := #[`CooperativeGames.*]
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
-- A ce stade, le seul `lean_lib` est `StableMarriage` (vide, juste pour
-- valider le wiring) ; aucun import reel de `stable_marriage_lean/...`
-- pour eviter couplage circular lake (chaque absorption = PR separe).
--
-- Convention i18n EPIC #4980 (cf decision_theory_lean precedent) :
-- `globs` (et non `roots`) avec suffixe `.*` pour auto-decouvrir siblings `_en`.
-- Aplicable des qu'un premier module absorbe arrive (c.300+).
@[default_target]
lean_lib StableMarriage where
  globs := #[`StableMarriage.*]
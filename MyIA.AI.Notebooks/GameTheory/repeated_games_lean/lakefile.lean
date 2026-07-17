import Lake
open Lake DSL

package «repeated_games» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

-- Convention i18n EPIC #4980 (ratifiee ai-01 2026-07-04, comment-4881909354) :
-- chaque `Foo.lean` FR canonique a un sibling `Foo_en.lean` (miroir EN, namespace
-- `_en`) qui doit compiler dans le meme lake. Pour que `lake build` les decouvre
-- automatiquement (sinon seuls les modules explicitement importes par la racine
-- sont built -- ici la racine importe Stage/Discounting/GrimTrigger/Folk, PAS les
-- `_en`), on utilise `globs` plutot que les roots par defaut.
--
-- NOTE technique (validee firsthand po-2026 c.218, PR #5360) : la forme bare
-- `globs := #[`<Lib>]` NE fonctionne PAS -- elle ne matche que le module root,
-- pas les enfants. Il FAUT le suffixe `.*` : `globs := #[`<Lib>.*]`. Regle Lake :
-- `Glob.one` `` `Foo `` = module Foo seul ; `` `Foo.* `` = Foo + children.
--
-- EPIC #4365 Phase-4 (PR #6146, 2026-07-15) : RepeatedGames a ete absorbe byte-identique
-- dans `game_theory_lean/RepeatedGames/`, qui est desormais le home canonique
-- (`@[default_target] lean_lib RepeatedGames` dans game_theory_lean/lakefile.lean).
-- L'ancienne declaration `lean_lib «RepeatedGames»` ci-dessous est NEUTRALISEE :
-- ses `globs` pointaient vers les 4 modules (Stage/Discounting/GrimTrigger/Folk) dont
-- les sources ont ete deplacees, donc `RepeatedGames.*` matche 0 fichier dans CE lake
-- (0 module .lean restant, seul ce lakefile.lean de config). Build depuis ce lake
-- produirait une lib vide ET menacerait une collision de module-path avec le home
-- canonique. Ce lake archive conserve son `package`, son `require mathlib`, ses
-- docs/manifest/toolchain (coquille archive) mais n'expose PLUS la lib. La
-- certification no-sorry (grim_trigger_sustains_iff, theoreme-phare) et le Lake build
-- sont repris par game_theory_lean via `.github/workflows/lean-repeated-games.yml`.
-- -- @[default_target]
-- -- lean_lib «RepeatedGames» where
-- --   globs := #[`RepeatedGames.*]  (archive, voir git history PR #6146)


import Lake
open Lake DSL

package «repeated_games» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

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
@[default_target]
lean_lib «RepeatedGames» where
  -- Repeated Games Library for Lean 4
  -- Includes: stage game (Prisoner's Dilemma), discounting, grim trigger
  -- Theorem phare: grim_trigger_sustains_iff (one-shot deviation principle)
  globs := #[`RepeatedGames.*]

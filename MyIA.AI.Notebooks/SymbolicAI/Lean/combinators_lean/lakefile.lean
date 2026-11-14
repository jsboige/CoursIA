import Lake
open Lake DSL

package «combinators» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

-- Pin explicite v4.33.0 (même convention que conway_lean, harmonisation #4362) :
-- sans `@`, lake résout la require sur `master` alors que le manifest est
-- épinglé, d'où un warning `manifest out of date` à chaque build.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

@[default_target]
lean_lib «Combinators» where
  -- Pas de jumeaux `_en` (rollout i18n DRAINED, FR par défaut) : la glob
  -- couvre les sous-modules et le fichier racine `Combinators.lean`.
  globs := #[.submodules `Combinators, `Combinators]

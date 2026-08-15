import Lake
open Lake DSL

package «galois» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

-- Bare `lean_lib` (no `globs`): the root aggregator `Galois.lean` imports the
-- vendored module(s), so `lake build` (default target) builds the full proof via
-- the root's import closure — mirroring conway_lean / cooperative_games_lean.
-- NB: the glob form `globs := #[`Galois.*]` triggers a lake v4.31.0-rc1 job-
-- computation trace quirk ("some modules have bad imports") on this single-
-- module lake, even though every module compiles cleanly; the bare-lib +
-- root-aggregator path sidesteps it. Sibling `_en` modules (i18n #4980) will be
-- imported here when added. Cf grothendieck_lean (#6154) for the glob form.
@[default_target]
lean_lib «Galois» where

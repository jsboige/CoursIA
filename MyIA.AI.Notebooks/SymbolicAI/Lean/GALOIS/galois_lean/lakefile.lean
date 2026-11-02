import Lake
open Lake DSL

package «galois» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

-- `globs := #[`Galois.*]` auto-discovers every submodule under `Galois/`,
-- including the `_en` i18n siblings (#4980, added with the adic-completion
-- layer #14783) — same pattern as game_theory_lean / decision_theory_lean.
-- History: the lake started bare-lib (root aggregator only) because the glob
-- form tripped a lake v4.31.0-rc1 job-computation quirk ("some modules have
-- bad imports"); at v4.33.0 the glob build is verified SUCCESS. The bare-lib
-- escape is no longer viable anyway: `check_en_built` in
-- scripts/lean/check_i18n_siblings.py reads roots/globs only, so a root-import
-- `_en` mirror would be flagged UNBUILT by the lean-i18n-drift CI gate even
-- though `lake build` compiles it.
@[default_target]
lean_lib «Galois» where
  globs := #[`Galois.*]

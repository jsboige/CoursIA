import Lake
open Lake DSL

package percolation_lean where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.unicode.fun, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

-- Convention i18n EPIC #4980 : `globs` (et non `roots`) pour que `lake build`
-- auto-découvre les siblings `_en` (miroir EN, namespace `Percolation`_en).
-- `Percolation.*` couvre les modules NESTED (`Percolation/Basic_en.lean` ->
-- `Percolation.Basic_en`), le bare `Percolation_en` couvre le root aggregator
-- EN (`Percolation_en.lean`). Cf. decision_theory_lean (template de la famille).
@[default_target]
lean_lib Percolation where
  globs := #[`Percolation.*, `Percolation_en]

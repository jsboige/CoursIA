import Lake
open Lake DSL

package decision_theory_lean where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.unicode.fun, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc2"

@[default_target]
lean_lib Gittins where
  roots := #[`Gittins]

@[default_target]
lean_lib Utility where
  roots := #[`Utility]

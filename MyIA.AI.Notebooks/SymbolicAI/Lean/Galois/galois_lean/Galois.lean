/-
Root aggregator for the `galois_lean` lake (proof layer for Lean-19, inverse
Galois problem / M23). Imports the vendored upstream M23 proof bundle so that
`lake build` (the `lean_lib Galois` default target, `globs := #[`Galois.*]`)
builds the full proof. The glob form is the current one, verified SUCCESS at
v4.33.0; the bare-lib escape is historical and consigned in `lakefile.lean`.

The adic-completion layer (#14783) adds the FR/EN sibling pair
`AdicCompletionLocalRing.lean` / `AdicCompletionLocalRing_en.lean` (i18n
#4980): both are self-contained and imported here. The lower-ramification
layer (#14786) adds the sibling pair `LowerRamificationGroup.lean` /
`LowerRamificationGroup_en.lean`.
-/
import Galois.M23Lean4Web
import Galois.AdicCompletionLocalRing
import Galois.AdicCompletionLocalRing_en
import Galois.LowerRamificationGroup
import Galois.LowerRamificationGroup_en

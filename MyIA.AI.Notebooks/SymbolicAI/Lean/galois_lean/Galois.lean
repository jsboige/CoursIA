/-
Root aggregator for the `galois_lean` lake (proof layer for Lean-19, inverse
Galois problem / M23). Imports the vendored upstream M23 proof bundle so that
`lake build` (the bare `lean_lib Galois` default target) builds the full proof
without a glob — mirroring the conway_lean / cooperative_games_lean layout.

The adic-completion layer (#14783) adds the FR/EN sibling pair
`AdicCompletionLocalRing.lean` / `AdicCompletionLocalRing_en.lean` (i18n
#4980): both are self-contained and imported here.
-/
import Galois.M23Lean4Web
import Galois.AdicCompletionLocalRing
import Galois.AdicCompletionLocalRing_en

/-
Root aggregator for the `galois_lean` lake (proof layer for Lean-19, inverse
Galois problem / M23). Imports the vendored upstream M23 proof bundle so that
`lake build` (the bare `lean_lib Galois` default target) builds the full proof
without a glob — mirroring the conway_lean / cooperative_games_lean layout.
-/
import Galois.M23Lean4Web

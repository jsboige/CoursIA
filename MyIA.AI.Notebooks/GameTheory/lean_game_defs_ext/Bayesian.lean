/-
  Bayesian Games — root module
  ============================

  Core-Lean-4-only formalization of finite two-player Bayesian games
  (Harsanyi type spaces, interim expected utility, Bayesian Nash
  equilibrium). Companion to GameTheory-11-BayesianGames.ipynb.

  Modules:
  - `Bayesian.Sum`      — finite sums over `Fin n` with the lemmas we need
  - `Bayesian.Types`    — `BayesGame2`, strategies, interim/ex-ante utility
  - `Bayesian.BNE`      — decidable `isBNE`, one-shot deviation principle,
                          prior-rescaling invariance
  - `Bayesian.Examples` — Battle of the Sexes with incomplete information,
                          equilibrium certified by `decide`

  See #2610 (GT-Lean formalization, phase 1: Bayesian games).
-/

import Bayesian.Sum
import Bayesian.Types
import Bayesian.BNE
import Bayesian.Examples

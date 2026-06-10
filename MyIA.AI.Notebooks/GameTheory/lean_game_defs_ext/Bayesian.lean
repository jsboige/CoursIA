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
  - `Bayesian.Auction`  — first-price sealed-bid auction: truthful bidding
                          earns zero (general theorem), bid-shading BNE
                          certified by `decide` (phase 2)
  - `Bayesian.Vickrey`  — second-price auction: truthful bidding weakly
                          dominant, BNE for every `n` (phase 3)

  See #2610 (GT-Lean formalization, phases 1-3: Bayesian games).
-/

import Bayesian.Sum
import Bayesian.Types
import Bayesian.BNE
import Bayesian.Examples
import Bayesian.Auction
import Bayesian.Vickrey

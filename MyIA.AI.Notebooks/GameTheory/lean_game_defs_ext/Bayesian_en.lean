import Bayesian.Sum
import Bayesian.Types
import Bayesian.BNE
import Bayesian.Examples
import Bayesian.Auction
import Bayesian.Vickrey
import Bayesian.Max
import Bayesian.Information
import Bayesian.InfoGames
import Bayesian.Reputation
import Bayesian.Regret
import Bayesian.FictitiousPlay

/-!
  Bayesian Games — root module
  ============================

  English mirror of `Bayesian.lean` (FR-first canonical). This file is a
  landing-doc mirror: only the module docstring differs from the FR version.
  Body signatures, proofs, and tactics remain byte-identical between the two
  files.

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
  - `Bayesian.Max`      — finite maxima over `Fin (n + 1)`, max-of-sum
                          vs sum-of-maxima (phase 4)
  - `Bayesian.Information` — value of information for a single decision
                          maker: signals as partitions, Blackwell
                          monotonicity, no-info ≤ signal ≤ perfect (phase 4)
  - `Bayesian.InfoGames` — counterexample: in a *game*, more information
                          can strictly hurt the informed player (unique
                          BNE payoffs 3 < 5, kernel-checked) (phase 4)
  - `Bayesian.Reputation` — entry deterrence / chain-store reputation:
                          unique credible BNE with and without type
                          uncertainty, reputation pays 5 > 4 (phase 5)
  - `Bayesian.Regret`   — external regret of a finite play sequence (basis
                          of regret minimization / CFR): defining bound,
                          max-characterization, `decide`-certified examples
                          (phase 6, GT-13 target)
  - `Bayesian.FictitiousPlay` — foundational no-regret learning algorithm:
                          born-correct state, empirical beliefs, elementary
                          step, counting invariant certified by `decide`,
                          2×2 example (phase 7, GT-17 target)

  See #2610 (GT-Lean formalization, phases 1-7: Bayesian games + regret +
  Fictitious Play).

  Convention i18n (EPIC #4980, decision ratified 2026-07-04, see
  `code-style.md` §Lean i18n): distinct FR+EN sibling files (`Bayesian.lean`
  / `Bayesian_en.lean`) — no inline bilingual block in a single file
  (Option B rejected: double cost + FR/EN drift + quality bias).
-/

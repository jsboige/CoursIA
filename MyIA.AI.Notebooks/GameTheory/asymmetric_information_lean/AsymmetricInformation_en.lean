/-
  AsymmetricInformation — root module (FR canonical)
  =====================================================

  Aggregator of the `asymmetric_information_lean/` lake, first formal
  delivery of the founding models of informational asymmetry (Akerlof
  1970, Spence 1973, Rothschild-Stiglitz 1976, Wilson-Miyazaki-Spence
  1977-1978) under the upstream Bayesian API `lean_game_defs_ext.Bayesian`.

  Modules:
  - `AsymmetricInformation.Lemons` — Akerlof 1970 model, fixed point on
    participation regions, accepted multiplicity, **NO** auxiliary clause
    in κ.
  - `AsymmetricInformation.Signaling` — Spence 1973 model, competitive
    wage `w_q = y_q`, 4 explicit constraints, Riley least-cost separator
    on a finite instance.
  - `AsymmetricInformation.Screening` — RS 1976 model, Nash among insurers,
    break-even type-by-type, **NO** cross-subsidy.
  - `AsymmetricInformation.MiyazakiWilson` — anticipatory 1977-1978,
    cross-subsidy tenable, **NO** general existence/uniqueness claim.
  - `AsymmetricInformation.BayesianLink` — non-vacuous bridge to
    `lean_game_defs_ext.Bayesian`: `bridgeGame : BayesGame2` instance,
    strategies, `theorem bridgeStrategy_isBNE := by decide`.

  i18n convention (EPIC #4980, user decision 2026-07-04): this root
  aggregator file is **FR canonical**, with its English mirror in the
  sibling file `AsymmetricInformation_en.lean` (sibling pair model
  ratified 2026-07-04, cf `code-style.md` §Lean i18n).
-/

import AsymmetricInformation.Lemons
import AsymmetricInformation.Signaling
import AsymmetricInformation.Screening
import AsymmetricInformation.MiyazakiWilson
import AsymmetricInformation.BayesianLink
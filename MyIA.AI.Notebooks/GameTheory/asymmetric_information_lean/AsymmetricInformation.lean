/-
  AsymmetricInformation — module racine (FR canonique)
  =====================================================

  Aggregator du lake `asymmetric_information_lean/`, première livraison
  formelle des modèles fondateurs d'asymétrie informationnelle (Akerlof
  1970, Spence 1973, Rothschild-Stiglitz 1976, Wilson-Miyazaki-Spence
  1977-1978) sous l'API bayésienne amont `lean_game_defs_ext.Bayesian`.

  Modules :
  - `AsymmetricInformation.Lemons` — modèle Akerlof 1970, point fixe sur
    les régions de participation, multiplicité acceptée, **aucune** clause
    auxiliaire dans κ.
  - `AsymmetricInformation.Signaling` — modèle Spence 1973, salaire
    concurrentiel `w_q = y_q`, 4 contraintes explicites, séparateur de
    coût minimal de Riley sur une instance finie.
  - `AsymmetricInformation.Screening` — modèle RS 1976, Nash parmi les
    assureurs, break-even type par type, **aucun** cross-subsidy.
  - `AsymmetricInformation.MiyazakiWilson` — anticipation 1977-1978,
    cross-subsidy tenable, **aucune** affirmation d'existence/unicité
    générale.
  - `AsymmetricInformation.BayesianLink` — pont non vide vers
    `lean_game_defs_ext.Bayesian` : instance `bridgeGame : BayesGame2`,
    stratégies, `theorem bridgeStrategy_isBNE := by decide`.

  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier root
  aggregator est **FR canonique**, avec son miroir anglais dans le fichier
  sibling `AsymmetricInformation_en.lean` (modèle sibling pair ratifié
  2026-07-04, cf `code-style.md` §Lean i18n).
-/

import AsymmetricInformation.Lemons
import AsymmetricInformation.Signaling
import AsymmetricInformation.Screening
import AsymmetricInformation.MiyazakiWilson
import AsymmetricInformation.BayesianLink
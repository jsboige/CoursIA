/-
  AsymmetricInformation — module racine (FR canonique)
  =====================================================

  Aggregator du lake `asymmetric_information_lean/`, première livraison
  formelle des modèles fondateurs d'asymétrie informationnelle (Akerlof
  1970, Spence 1973, Rothschild-Stiglitz 1976, Wilson-Miyazaki-Spence
  1977-1978) sous l'API bayésienne amont `lean_game_defs_ext.Bayesian`.

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
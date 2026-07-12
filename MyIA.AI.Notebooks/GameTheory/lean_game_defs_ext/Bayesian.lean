/-
  Jeux bayésiens — module racine
  ==============================

  Formalisation en Lean 4 core uniquement (sans Mathlib) des jeux
  bayésiens finis à deux joueurs (espaces de types de Harsanyi, utilité
  espérée interimaire, équilibre de Nash bayésien). Compagnon du
  notebook GameTheory-11-BayesianGames.ipynb.

  Modules :
  - `Bayesian.Sum`      — sommes finies sur `Fin n` avec les lemmes requis
  - `Bayesian.Types`    — `BayesGame2`, stratégies, utilité interim/ex-ante
  - `Bayesian.BNE`      — `isBNE` décidable, principe de déviation unique,
                          invariance par remise à l'échelle du prior
  - `Bayesian.Examples` — Bataille des Sexes en information incomplète,
                          équilibre certifié par `decide`
  - `Bayesian.Auction`  — enchère scellée au premier prix : l'offre sincère
                          rapporte zéro (théorème général), BNE de shading
                          d'offre certifié par `decide` (phase 2)
  - `Bayesian.Vickrey`  — enchère au second prix : l'offre sincère est
                          faiblement dominante, BNE pour tout `n` (phase 3)
  - `Bayesian.Max`      — maxima finis sur `Fin (n + 1)`, max-de-la-somme
                          vs somme-des-max (phase 4)
  - `Bayesian.Information` — valeur de l'information pour un décideur
                          unique : signaux comme partitions, monotonie de
                          Blackwell, pas-d'info ≤ signal ≤ parfait (phase 4)
  - `Bayesian.InfoGames` — contre-exemple : dans un *jeu*, plus
                          d'information peut nuire strictement au joueur
                          informé (paiements de BNE unique 3 < 5,
                          vérifié au noyau) (phase 4)
  - `Bayesian.Reputation` — dissuasion d'entrée / réputation de la firme
                          établie : BNE crédible unique avec et sans
                          incertitude sur le type, la réputation paie 5 > 4
                          (phase 5)

  Voir #2610 (formalisation GT-Lean, phases 1-5 : jeux bayésiens).

  ---
  English:
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

  See #2610 (GT-Lean formalization, phases 1-5: Bayesian games).
-/

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

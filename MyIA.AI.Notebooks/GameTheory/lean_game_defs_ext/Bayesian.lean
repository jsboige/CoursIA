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
  - `Bayesian.Regret`   — regret externe d'une suite finie de jeu (base de
                          la minimisation de regret / CFR) : borne
                          définissante, caractérisation par le max, exemples
                          certifiés par `decide` (phase 6, cible GT-13)
  - `Bayesian.FictitiousPlay` — algorithme fondateur de l'apprentissage
                          no-regret : état born-correct, croyances
                          empiriques, étape élémentaire, invariant de
                          comptage certifié par `decide`, exemple 2×2
                          (phase 7, cible GT-17)

  Voir #2610 (formalisation GT-Lean, phases 1-7 : jeux bayésiens + regret
  + Fictitious Play).

  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier root
  aggregator est **FR canonique**, avec son miroir anglais dans le fichier
  sibling `Bayesian_en.lean` (modèle sibling pair ratifié 2026-07-04, cf
  `code-style.md` §Lean i18n). Les modules substantiels vivent dans des
  fichiers siblings `_en.lean` séparés (découverts par le `globs` du
  lakefile).
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
import Bayesian.Regret
import Bayesian.FictitiousPlay

/-
  Espaces de types de Harsanyi — jeux bayésiens finis à deux joueurs
  =================================================================

  Formalise les jeux à information incomplète (Harsanyi 1967) pour le cas
  fini à deux joueurs, en Lean 4 core (sans Mathlib) :

  - `BayesGame2` : ensembles de types, ensembles d'actions, un prior commun
    non normalisé donné par des poids `Nat`, et des paiements dépendant du type
  - `Strategy1` / `Strategy2` : stratégies pures contingentes au type
  - `interimU1` / `interimU2` : utilité espérée interimaire (conditionnée par
    son propre type), comme une somme pondérée sur les types de l'adversaire
  - `exAnteU1` / `exAnteU2` : utilité espérée ex-ante

  Travailler avec des poids entiers plutôt qu'avec une mesure de probabilité
  normalisée garde toute quantité calculable et décidable ; `BNE.lean` prouve
  que les meilleures réponses sont invariantes par remise à l'échelle du prior,
  ce qui est exactement ce que signifie l'indépendance vis-à-vis de la
  normalisation.

  Basé sur GameTheory-11-BayesianGames.ipynb. Voir #2610 (phase 1 :
  jeux bayésiens — le rapport de recherche recommande les types finis d'abord).

  ---
  English:
  Harsanyi Type Spaces — Two-Player Finite Bayesian Games
  =======================================================

  Formalizes games of incomplete information (Harsanyi 1967) for the
  two-player finite case, in core Lean 4 (no Mathlib):

  - `BayesGame2`: type sets, action sets, an unnormalized common prior
    given by `Nat` weights, and type-dependent payoffs
  - `Strategy1` / `Strategy2`: pure type-contingent strategies
  - `interimU1` / `interimU2`: interim expected utility (conditional on
    one's own type), as a weight-sum over the opponent's types
  - `exAnteU1` / `exAnteU2`: ex-ante expected utility

  Working with integer weights instead of a normalized probability
  measure keeps every quantity computable and decidable; `BNE.lean`
  proves that best responses are invariant under rescaling the prior,
  which is exactly what normalization-independence means.

  Based on GameTheory-11-BayesianGames.ipynb. See #2610 (phase 1:
  Bayesian games — research report recommends finite types first).
-/

import Bayesian.Sum

/-- Un jeu bayésien fini à deux joueurs avec un prior non normalisé.

    Le joueur 1 a `nT1` types possibles et `nA1` actions ; le joueur 2 a
    `nT2` types et `nA2` actions. `w t1 t2` est le poids (non normalisé,
    `Nat`) du prior pour le profil de types `(t1, t2)`. Les paiements
    dépendent du profil de types complet et du profil d'actions.

    English: A two-player finite Bayesian game with an unnormalized prior.

    Player 1 has `nT1` possible types and `nA1` actions; player 2 has
    `nT2` types and `nA2` actions. `w t1 t2` is the (unnormalized,
    `Nat`) prior weight of the type profile `(t1, t2)`. Payoffs depend
    on the full type profile and the action profile. -/
structure BayesGame2 where
  /-- Nombre de types du joueur 1.
      English: Number of types of player 1 -/
  nT1 : Nat
  /-- Nombre de types du joueur 2.
      English: Number of types of player 2 -/
  nT2 : Nat
  /-- Nombre d'actions du joueur 1.
      English: Number of actions of player 1 -/
  nA1 : Nat
  /-- Nombre d'actions du joueur 2.
      English: Number of actions of player 2 -/
  nA2 : Nat
  /-- Prior commun sur les profils de types, comme poids non normalisés.
      English: Common prior over type profiles, as unnormalized weights -/
  w : Fin nT1 → Fin nT2 → Nat
  /-- Paiement du joueur 1.
      English: Payoff of player 1 -/
  u1 : Fin nT1 → Fin nT2 → Fin nA1 → Fin nA2 → Int
  /-- Paiement du joueur 2.
      English: Payoff of player 2 -/
  u2 : Fin nT1 → Fin nT2 → Fin nA1 → Fin nA2 → Int

/-- Une stratégie pure contingente au type du joueur 1 : son propre type → action.
    English: A pure type-contingent strategy of player 1: own type → action. -/
def Strategy1 (g : BayesGame2) := Fin g.nT1 → Fin g.nA1

/-- Une stratégie pure contingente au type du joueur 2 : son propre type → action.
    English: A pure type-contingent strategy of player 2: own type → action. -/
def Strategy2 (g : BayesGame2) := Fin g.nT2 → Fin g.nA2

/-- Utilité espérée interimaire du joueur 1 : de type `t1`, jouant l'action
    `a`, face à la stratégie `s2`, pondérée par la ligne du prior `w t1 ·`.

    (Avec des poids non normalisés, c'est l'espérance conditionnelle
    mise à l'échelle par la constante positive `Σ_{t2} w t1 t2` — les
    maximiseurs ne sont pas affectés, voir `BNE.lean`.)

    English: Interim expected utility of player 1: of type `t1`, playing action
    `a`, against strategy `s2`, weighted by the prior row `w t1 ·`.

    (With unnormalized weights this is the conditional expectation
    scaled by the positive constant `Σ_{t2} w t1 t2` — maximizers are
    unaffected, see `BNE.lean`.) -/
def interimU1 (g : BayesGame2) (t1 : Fin g.nT1) (a : Fin g.nA1)
    (s2 : Strategy2 g) : Int :=
  sumFin g.nT2 (fun t2 => (g.w t1 t2 : Int) * g.u1 t1 t2 a (s2 t2))

/-- Utilité espérée interimaire du joueur 2 : de type `t2`, jouant l'action
    `a`, face à la stratégie `s1`, pondérée par la colonne du prior `w · t2`.
    English: Interim expected utility of player 2: of type `t2`, playing action
    `a`, against strategy `s1`, weighted by the prior column `w · t2`. -/
def interimU2 (g : BayesGame2) (t2 : Fin g.nT2) (a : Fin g.nA2)
    (s1 : Strategy1 g) : Int :=
  sumFin g.nT1 (fun t1 => (g.w t1 t2 : Int) * g.u2 t1 t2 (s1 t1) a)

/-- Utilité espérée ex-ante du joueur 1 sous un profil de stratégies :
    somme des utilités interimbaires sur les propres types du joueur 1.
    English: Ex-ante expected utility of player 1 under a strategy profile:
    sum of interim utilities over player 1's own types. -/
def exAnteU1 (g : BayesGame2) (s1 : Strategy1 g) (s2 : Strategy2 g) : Int :=
  sumFin g.nT1 (fun t1 => interimU1 g t1 (s1 t1) s2)

/-- Utilité espérée ex-ante du joueur 2 sous un profil de stratégies.
    English: Ex-ante expected utility of player 2 under a strategy profile. -/
def exAnteU2 (g : BayesGame2) (s1 : Strategy1 g) (s2 : Strategy2 g) : Int :=
  sumFin g.nT2 (fun t2 => interimU2 g t2 (s2 t2) s1)

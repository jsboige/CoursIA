/-
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

/-- A two-player finite Bayesian game with an unnormalized prior.

    Player 1 has `nT1` possible types and `nA1` actions; player 2 has
    `nT2` types and `nA2` actions. `w t1 t2` is the (unnormalized,
    `Nat`) prior weight of the type profile `(t1, t2)`. Payoffs depend
    on the full type profile and the action profile. -/
structure BayesGame2 where
  /-- Number of types of player 1 -/
  nT1 : Nat
  /-- Number of types of player 2 -/
  nT2 : Nat
  /-- Number of actions of player 1 -/
  nA1 : Nat
  /-- Number of actions of player 2 -/
  nA2 : Nat
  /-- Common prior over type profiles, as unnormalized weights -/
  w : Fin nT1 → Fin nT2 → Nat
  /-- Payoff of player 1 -/
  u1 : Fin nT1 → Fin nT2 → Fin nA1 → Fin nA2 → Int
  /-- Payoff of player 2 -/
  u2 : Fin nT1 → Fin nT2 → Fin nA1 → Fin nA2 → Int

/-- A pure type-contingent strategy of player 1: own type → action. -/
def Strategy1 (g : BayesGame2) := Fin g.nT1 → Fin g.nA1

/-- A pure type-contingent strategy of player 2: own type → action. -/
def Strategy2 (g : BayesGame2) := Fin g.nT2 → Fin g.nA2

/-- Interim expected utility of player 1: of type `t1`, playing action
    `a`, against strategy `s2`, weighted by the prior row `w t1 ·`.

    (With unnormalized weights this is the conditional expectation
    scaled by the positive constant `Σ_{t2} w t1 t2` — maximizers are
    unaffected, see `Beliefs.lean`.) -/
def interimU1 (g : BayesGame2) (t1 : Fin g.nT1) (a : Fin g.nA1)
    (s2 : Strategy2 g) : Int :=
  sumFin g.nT2 (fun t2 => (g.w t1 t2 : Int) * g.u1 t1 t2 a (s2 t2))

/-- Interim expected utility of player 2: of type `t2`, playing action
    `a`, against strategy `s1`, weighted by the prior column `w · t2`. -/
def interimU2 (g : BayesGame2) (t2 : Fin g.nT2) (a : Fin g.nA2)
    (s1 : Strategy1 g) : Int :=
  sumFin g.nT1 (fun t1 => (g.w t1 t2 : Int) * g.u2 t1 t2 (s1 t1) a)

/-- Ex-ante expected utility of player 1 under a strategy profile:
    sum of interim utilities over player 1's own types. -/
def exAnteU1 (g : BayesGame2) (s1 : Strategy1 g) (s2 : Strategy2 g) : Int :=
  sumFin g.nT1 (fun t1 => interimU1 g t1 (s1 t1) s2)

/-- Ex-ante expected utility of player 2 under a strategy profile. -/
def exAnteU2 (g : BayesGame2) (s1 : Strategy1 g) (s2 : Strategy2 g) : Int :=
  sumFin g.nT2 (fun t2 => interimU2 g t2 (s2 t2) s1)

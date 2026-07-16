/-
  Regret Minimization and CFR Definitions in Lean 4
  ==================================================

  Defines structures for regret-based learning in games:
  - Regret: Difference between achieved and best possible payoff
  - RegretMatching: Strategy update rule from cumulative regrets
  - CFR (Counterfactual Regret Minimization): Key algorithm for
    solving imperfect-information games

  Based on GameTheory-13-ImperfectInfo-CFR.ipynb

  Note: These are pedagogical definitions. A full formalization would
  require measure theory and convergence proofs (not attempted here).

  ---
  i18n sibling: this module is the EN mirror of the FR canonical `Regret.lean`
  (sibling-pair Pattern A, ratified by user on 2026-07-04, EPIC #4980). The FR
  canonical lives in `Regret.lean` (top-level declarations, no namespace). This
  EN mirror uses the *reuse-FR-names* variant: it `import Basic` and
  `import Bayesian` (the FR canonical base modules that `Regret.lean` depends on)
  and reuses their identifiers verbatim, wrapping only its own new declarations
  in `namespace RegretEn` to avoid name collisions with the FR `Regret` module
  when both live in the same lake. The body of definitions, signatures and
  tactics is byte-identical between the two files; only the docstrings
  `/-! ... -/` (section headings) and `/-- ... -/` (declaration docstrings)
  differ — EN in this file, FR in `Regret.lean`.
-/

import Basic
import Bayesian

namespace RegretEn

/-!
## Regret Concepts
-/

/-- Instantaneous regret for an action: how much better that action
    would have been compared to what was actually played.

    regret(a) = u(a) - u(a_played)
-/
def instantRegret (payoff : Fin n → Float) (played : Fin n) (action : Fin n) : Float :=
  payoff action - payoff played

/-- Cumulative regret for each action over T iterations.
    Stored as a map from action index to accumulated regret. 
-/
def CumulativeRegret (n : Nat) := Fin n → Float

/-- Initialize zero regret -/
def zeroRegret (n : Nat) : CumulativeRegret n := fun _ => 0

/-- Update cumulative regret with a new observation -/
def updateRegret {n : Nat} (regret : CumulativeRegret n)
    (payoff : Fin n → Float) (played : Fin n) : CumulativeRegret n :=
  fun a => regret a + instantRegret payoff played a

/-!
## Regret Matching
-/

/-- Regret matching: convert positive cumulative regrets to a strategy.

    For each action a: σ(a) = R+(a) / Σ_a' R+(a')
    where R+ is the positive part of cumulative regret.

    If all regrets are non-positive, play uniformly.
-/
def regretMatchingStrategy {n : Nat} (regret : CumulativeRegret n) : Fin n → Float :=
  let posRegret (a : Fin n) : Float := max 0 (regret a)
  let total := (List.finRange n).foldl (fun acc a => acc + posRegret a) 0
  if total > 0 then
    fun a => posRegret a / total
  else
    fun _ => (1.0 : Float) / n.toFloat  -- uniforme

/-!
## External Regret (Hannan Consistency)
-/

/-- External regret: difference between realized payoff and best
    fixed action in hindsight.

    R_T = max_a Σ_t u_t(a) - Σ_t u_t(a_t)
-/
def externalRegret (T : Nat) (payoffs : Fin T → (Fin n → Float))
    (played : Fin T → Fin n) : Float :=
  let bestFixed := (List.finRange n).foldl
    (fun acc a => max acc ((List.finRange T).foldl
      (fun s t => s + payoffs t a) 0))
    0
  let realized := (List.finRange T).foldl
    (fun s t => s + payoffs t (played t)) 0
  bestFixed - realized

/-!
## Counterfactual Regret
-/

/-- Counterfactual regret for a player at an information set.

    The key insight of CFR: minimize counterfactual regret at each
    information set independently, and the average strategy converges
    to a Nash equilibrium in two-player zero-sum games.

    CFR(I, a) = Σ_z∈Z_I  π_{-i}(z) · (u_i(z, a) - u_i(z, σ(I)))

    where π_{-i} is the reach probability excluding player i.
-/
structure CounterfactualRegret where
  /-- The information set identifier -/
  infoSet : String
  /-- The player -/
  player : Nat
  /-- Regret for each available action -/
  actionRegrets : List (String × Float)  -- (nom_action, valeur_regret)
  deriving Repr

/-!
## CFR Solver State
-/

/-- The state maintained by a CFR solver across iterations -/
structure CFRState where
  /-- Cumulative counterfactual regret per information set and action -/
  cumulativeRegret : List (String × List (String × Float))
  /-- Cumulative strategy (sum of strategies weighted by reach) -/
  strategySum : List (String × List (String × Float))
  /-- Number of iterations completed -/
  iterations : Nat
  deriving Repr

/-- Initialize empty CFR state -/
def initCFRState : CFRState where
  cumulativeRegret := []
  strategySum := []
  iterations := 0

/-!
## Convergence Concepts
-/

/-- Average regret approaches zero (ε-Nash equilibrium) -/
def epsilonNash (ε : Float) (externalReg : Float) : Prop :=
  externalReg <= ε

/-- No-regret learning: average external regret goes to zero.
    Payoffs and plays are indexed by `Nat` (infinite horizon); the regret
    at horizon `t` is computed on the prefix of the first `t` rounds. 
-/
def noRegret (payoffs : Nat → (Fin n → Float))
    (played : Nat → Fin n) : Prop :=
  ∀ ε > 0, ∃ T0, ∀ t ≥ T0,
    externalRegret t (fun s => payoffs s.val) (fun s => played s.val) / t.toFloat < ε

/-!
## Fictitious Play (from GT-17 Section 3)
-/

/-- Fictitious play: each player plays best response to the
    empirical distribution of opponent's past plays.

    Brown (1951): converges to Nash equilibrium in:
    - 2-player zero-sum games
    - 2x2 games
    - Games with identical interests
-/
structure FictitiousPlayState (n : Nat) where
  /-- Empirical frequency of each player's actions -/
  actionCounts : Fin n → (Fin m → Nat)
  /-- Number of rounds played -/
  rounds : Nat
  -- pas de `deriving Repr` : `actionCounts` est un type fonctionnel, non dérivable

/-- Best response to empirical distribution of opponent.

    Conceptually: argmax_a Σ_{a_{-i}} empiricalDist(a_{-i}) · u_i(a, a_{-i}).
    In a full formalization this would use Mathlib's argmax.
-/
def isBestResponseToEmpirical {m : Nat}
    (payoff : Fin 2 → (Fin 2 → Fin m) → Float)
    (empiricalDist : Fin 2 → (Fin m → Float))
    (player : Fin 2) (action : Fin m) : Prop :=
  ∀ other : Fin m,
    let expected := fun a =>
      (List.finRange m).foldl
        (fun acc a' => acc + empiricalDist (if player.val = 0 then 1 else 0) a' *
                       payoff player (fun j => if j = player then a else a'))
        0
    expected action >= expected other

end RegretEn

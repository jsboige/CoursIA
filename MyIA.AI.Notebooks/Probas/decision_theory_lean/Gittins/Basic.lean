/-!
# Basic Definitions — Multi-Armed Bandits

Core types for the bandit problem: arms, instances, policies, and value functions.
No Mathlib dependency — pure Lean 4 definitions.
-/

namespace Gittins

/-- A bandit arm characterized by its true mean reward. -/
structure BanditArm where
  name : String
  trueMean : Float
  deriving Repr

/-- A bandit instance: a collection of arms with a discount factor. -/
structure BanditInstance where
  arms : Array BanditArm
  discount : Float  -- gamma in (0, 1)
  deriving Repr

/-- A policy maps each time step to the index of the arm to pull. -/
def Policy := Nat → Nat

/-- A reward history for a single arm. -/
def RewardHistory := List Float

/-- Number of times an arm has been pulled. -/
def pullCount (history : RewardHistory) : Nat := history.length

/-- Empirical mean from a reward history. Returns 0 for empty history. -/
def empiricalMean (history : RewardHistory) : Float :=
  match history with
  | [] => 0.0
  | _ => history.foldl (· + ·) 0.0 / history.length.toFloat

end Gittins

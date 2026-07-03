import Mathlib.Data.Real.Basic

/-!
# Basic Definitions — Multi-Armed Bandits

Core types for the bandit problem: arms, instances, policies, and value functions.
Means and discount factors are carried on `ℝ` (not `Float`) so that order laws are
reflexive — a bandit mean is a real number, never a `NaN`. Sampled reward histories
stay `Float` (empirical quantities); the two notions are deliberately distinct.
-/

namespace Gittins

/-- A bandit arm characterized by its true mean reward. -/
structure BanditArm where
  name : String
  trueMean : ℝ

/-- A bandit instance: a collection of arms with a discount factor. -/
structure BanditInstance where
  arms : Array BanditArm
  discount : ℝ  -- gamma in (0, 1)

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

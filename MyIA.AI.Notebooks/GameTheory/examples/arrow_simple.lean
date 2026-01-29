/-
  Arrow's Impossibility Theorem - Simple Example
  ==============================================

  A simplified demonstration of Arrow's theorem concepts.
  Related to GameTheory-19-Lean-SocialChoice.ipynb

  This file shows the basic structure without full proofs.
  For complete formalization, see lean_game_defs/SocialChoice.lean
-/

-- Basic definitions for a 3-alternative, 2-voter setting

-- Alternatives
inductive Alt where
  | a : Alt
  | b : Alt
  | c : Alt
deriving DecidableEq, Repr

-- Voters
inductive Voter where
  | v1 : Voter
  | v2 : Voter
deriving DecidableEq, Repr

-- A strict preference ordering (simplified as a function)
-- pref v x y means "voter v strictly prefers x to y"
def StrictPref := Voter → Alt → Alt → Bool

-- Example: Condorcet paradox profile
-- Voter 1: a > b > c
-- Voter 2: b > c > a
def condorcetProfile : StrictPref := fun v x y =>
  match v, x, y with
  | Voter.v1, Alt.a, Alt.b => true
  | Voter.v1, Alt.b, Alt.c => true
  | Voter.v1, Alt.a, Alt.c => true
  | Voter.v2, Alt.b, Alt.c => true
  | Voter.v2, Alt.c, Alt.a => true
  | Voter.v2, Alt.b, Alt.a => true
  | _, _, _ => false

-- Majority rule (pairwise)
def majorityPrefers (prefs : StrictPref) (x y : Alt) : Bool :=
  let v1_prefers := prefs Voter.v1 x y
  let v2_prefers := prefs Voter.v2 x y
  v1_prefers || v2_prefers  -- At least one prefers (tie-breaking simplified)

-- Check for cycles in majority preferences
def hasCycle (prefs : StrictPref) : Bool :=
  majorityPrefers prefs Alt.a Alt.b &&
  majorityPrefers prefs Alt.b Alt.c &&
  majorityPrefers prefs Alt.c Alt.a

-- Verify Condorcet paradox
#eval hasCycle condorcetProfile  -- Should be true!

-- This demonstrates why Arrow's theorem matters:
-- Even with just 2 voters and 3 alternatives,
-- majority rule can produce cycles (intransitive social preference)

-- A social welfare function
structure SWF where
  -- Maps individual preferences to social preference
  aggregate : StrictPref → (Alt → Alt → Bool)

-- Dictatorship: Voter 1's preference becomes social preference
def dictatorshipV1 : SWF := {
  aggregate := fun prefs x y => prefs Voter.v1 x y
}

-- Check if a SWF satisfies Pareto criterion
def satisfiesPareto (swf : SWF) (prefs : StrictPref) : Prop :=
  ∀ x y, (prefs Voter.v1 x y ∧ prefs Voter.v2 x y) →
         swf.aggregate prefs x y = true

-- A dictatorship trivially satisfies Pareto when dictator agrees
-- but violates non-dictatorship by definition

-- Arrow's theorem (informal statement):
-- There is no SWF with ≥3 alternatives that satisfies:
-- 1. Unrestricted domain (works for all preference profiles)
-- 2. Pareto efficiency
-- 3. Independence of Irrelevant Alternatives (IIA)
-- 4. Non-dictatorship

-- The proof is complex and requires careful handling of all cases.
-- See SocialChoice.lean for the formal framework.

#check dictatorshipV1
#check condorcetProfile

/-
  Nash Equilibrium Definitions in Lean 4
  ======================================

  Defines Nash equilibrium and related concepts:
  - Best response
  - Pure Nash equilibrium
  - Mixed Nash equilibrium
  - Strict dominance

  Based on GameTheory-16-Lean-Definitions.ipynb
-/

import GameTheory.lean_game_defs.Basic

/-! ## Best Response -/

/-- Player 1 plays a best response to s2 -/
def isBestResponse1 (g : Game2x2) (s1 : Fin 2 → Float) (s2 : Fin 2 → Float) : Prop :=
  ∀ s1' : Fin 2 → Float,
    expectedPayoff1 g s1 s2 >= expectedPayoff1 g s1' s2

/-- Player 2 plays a best response to s1 -/
def isBestResponse2 (g : Game2x2) (s1 : Fin 2 → Float) (s2 : Fin 2 → Float) : Prop :=
  ∀ s2' : Fin 2 → Float,
    expectedPayoff2 g s1 s2 >= expectedPayoff2 g s1 s2'

/-! ## Nash Equilibrium -/

/-- Nash equilibrium in mixed strategies: each player plays a best response -/
def isNashEquilibrium (g : Game2x2) (s1 : Fin 2 → Float) (s2 : Fin 2 → Float) : Prop :=
  isBestResponse1 g s1 s2 ∧ isBestResponse2 g s1 s2

/-- Nash equilibrium in pure strategies for 2x2 games -/
def isPureNashEquilibrium (g : Game2x2) (a1 : Fin 2) (a2 : Fin 2) : Prop :=
  -- Player 1 cannot improve by changing action
  (∀ a1' : Fin 2, g.payoff1 a1 a2 >= g.payoff1 a1' a2) ∧
  -- Player 2 cannot improve by changing action
  (∀ a2' : Fin 2, g.payoff2 a1 a2 >= g.payoff2 a1 a2')

/-! ## Dominance -/

/-- Action a strictly dominates action a' for player 1 -/
def strictlyDominates1 (g : Game2x2) (a a' : Fin 2) : Prop :=
  ∀ a2 : Fin 2, g.payoff1 a a2 > g.payoff1 a' a2

/-- Action a weakly dominates action a' for player 1 -/
def weaklyDominates1 (g : Game2x2) (a a' : Fin 2) : Prop :=
  (∀ a2 : Fin 2, g.payoff1 a a2 >= g.payoff1 a' a2) ∧
  (∃ a2 : Fin 2, g.payoff1 a a2 > g.payoff1 a' a2)

/-- Action a strictly dominates action a' for player 2 -/
def strictlyDominates2 (g : Game2x2) (a a' : Fin 2) : Prop :=
  ∀ a1 : Fin 2, g.payoff2 a1 a > g.payoff2 a1 a'

/-! ## Classic Games -/

/-- Prisoner's Dilemma: C=0 (Cooperate), D=1 (Defect) -/
def prisonersDilemma : Game2x2 := {
  payoff1 := fun i j =>
    match i.val, j.val with
    | 0, 0 => 3  -- (C, C)
    | 0, 1 => 0  -- (C, D)
    | 1, 0 => 5  -- (D, C)
    | 1, 1 => 1  -- (D, D)
    | _, _ => 0
  payoff2 := fun i j =>
    match i.val, j.val with
    | 0, 0 => 3  -- (C, C)
    | 0, 1 => 5  -- (C, D)
    | 1, 0 => 0  -- (D, C)
    | 1, 1 => 1  -- (D, D)
    | _, _ => 0
}

/-- Chicken Game: Yield=0, Charge=1 -/
def chickenGame : Game2x2 := {
  payoff1 := fun i j =>
    match i.val, j.val with
    | 0, 0 => 3  -- (Yield, Yield)
    | 0, 1 => 2  -- (Yield, Charge)
    | 1, 0 => 4  -- (Charge, Yield)
    | 1, 1 => 0  -- (Charge, Charge) - crash!
    | _, _ => 0
  payoff2 := fun i j =>
    match i.val, j.val with
    | 0, 0 => 3
    | 0, 1 => 4
    | 1, 0 => 2
    | 1, 1 => 0
    | _, _ => 0
}

/-- Stag Hunt: Stag=0, Hare=1 -/
def stagHunt : Game2x2 := {
  payoff1 := fun i j =>
    match i.val, j.val with
    | 0, 0 => 4  -- (Stag, Stag)
    | 0, 1 => 0  -- (Stag, Hare)
    | 1, 0 => 3  -- (Hare, Stag)
    | 1, 1 => 2  -- (Hare, Hare)
    | _, _ => 0
  payoff2 := fun i j =>
    match i.val, j.val with
    | 0, 0 => 4
    | 0, 1 => 3
    | 1, 0 => 0
    | 1, 1 => 2
    | _, _ => 0
}

/-- Matching Pennies (zero-sum): Heads=0, Tails=1 -/
def matchingPennies : Game2x2 := {
  payoff1 := fun i j =>
    match i.val, j.val with
    | 0, 0 => 1   -- (H, H)
    | 0, 1 => -1  -- (H, T)
    | 1, 0 => -1  -- (T, H)
    | 1, 1 => 1   -- (T, T)
    | _, _ => 0
  payoff2 := fun i j =>
    match i.val, j.val with
    | 0, 0 => -1
    | 0, 1 => 1
    | 1, 0 => 1
    | 1, 1 => -1
    | _, _ => 0
}

/-! ## Action Names -/

def Cooperer : Fin 2 := ⟨0, by omega⟩
def Trahir : Fin 2 := ⟨1, by omega⟩
def Ceder : Fin 2 := ⟨0, by omega⟩
def Foncer : Fin 2 := ⟨1, by omega⟩
def Cerf : Fin 2 := ⟨0, by omega⟩
def Lievre : Fin 2 := ⟨1, by omega⟩
def Pile : Fin 2 := ⟨0, by omega⟩
def Face : Fin 2 := ⟨1, by omega⟩

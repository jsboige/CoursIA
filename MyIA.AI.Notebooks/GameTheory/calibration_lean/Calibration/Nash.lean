/-
  Calibration Target: Nash Equilibrium in 2x2 Games
  ==================================================

  Self-contained definitions + calibration theorems for Prisoner's Dilemma.
  No external dependencies beyond Mathlib.

  Harness paths exercised:
  - Target C (strictly_domin_defect_pd): P3 — agent may search for
    nonexistent Mathlib game-theory lemmas; must fall back to case analysis.
  - Target D (pd_defect_is_pure_ne): P2 — multi-step proof requiring
    Fin 2 case splits and Int comparisons.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! ## Game Theory Definitions (self-contained) -/

/-- A 2x2 game: 2 players, 2 actions each -/
structure Game2x2 where
  payoff1 : Fin 2 → Fin 2 → Int
  payoff2 : Fin 2 → Fin 2 → Int

/-- Action a strictly dominates action a' for player 1 -/
def strictlyDominates1 (g : Game2x2) (a a' : Fin 2) : Prop :=
  ∀ a2 : Fin 2, g.payoff1 a a2 > g.payoff1 a' a2

/-- Nash equilibrium in pure strategies for 2x2 games -/
def isPureNashEquilibrium (g : Game2x2) (a1 : Fin 2) (a2 : Fin 2) : Prop :=
  (∀ a1' : Fin 2, g.payoff1 a1 a2 ≥ g.payoff1 a1' a2) ∧
  (∀ a2' : Fin 2, g.payoff2 a1 a2 ≥ g.payoff2 a1 a2')

/-! ## Prisoner's Dilemma -/

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

def Cooperer : Fin 2 := ⟨0, by omega⟩
def Trahir : Fin 2 := ⟨1, by omega⟩

/-! ## Calibration Targets -/

/-- Target C (P3): Strict dominance of defection in Prisoner's Dilemma.
    Exercises P3: agent may search Mathlib for game-theory lemmas that don't exist.
    Correct approach: unfold + Fin 2 case split + arithmetic.
    Expected iterations: 3-5 (search → fail → fallback → case split → close). -/
theorem strictly_domin_defect_pd :
    strictlyDominates1 prisonersDilemma Trahir Cooperer := by
  sorry

/-- Target D (P2): (D, D) is a pure Nash equilibrium of Prisoner's Dilemma.
    Exercises P2: requires Fin 2 case analysis + Int comparison across both players.
    Expected iterations: 4-7 (unfold → case split → arithmetic → close). -/
theorem pd_defect_is_pure_ne :
    isPureNashEquilibrium prisonersDilemma Trahir Trahir := by
  sorry

/-- Target E (P1+P2): (C, C) is NOT a pure Nash equilibrium.
    Harder: requires constructing a counterexample (defect beats cooperate).
    This exercises the prover's ability to prove NEGATIVE statements.
    Expected iterations: 5-10 (unfold → negation → construct witness → decide). -/
theorem pd_cooperate_not_ne :
    ¬ isPureNashEquilibrium prisonersDilemma Cooperer Cooperer := by
  sorry

/-! ## Sorry-Increase Calibration Target (P4) -/

/-- Target F (P4): sorry-increase case — harness must NOT revert when sorry count
    increases but build passes. This target is DESIGNED so the prover naturally
    decomposes the proof into two sub-goals (each player's incentive constraint).

    The prover should produce something like:
      constructor
      · sorry  -- player 1 has no incentive to deviate
      · sorry  -- player 2 has no incentive to deviate
    Which increases sorry 1→2 but compiles. Harness must preserve this.

    Expected iterations: 3-5 (unfold → constructor → 2 sorries → maybe prove one). -/
theorem pd_defect_is_ne_decomposable :
    isPureNashEquilibrium prisonersDilemma Trahir Trahir := by
  sorry

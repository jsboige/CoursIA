/-
  Cible de calibration : équilibre de Nash dans les jeux 2×2
  ===========================================================

  Définitions autonomes + théorèmes de calibration pour le dilemme du prisonnier.
  Aucune dépendance externe au-delà de Mathlib.

  Chemins du harnais exercés :
  - Cible C (strictly_domin_defect_pd) : P3 — l'agent peut rechercher des lemmes
    de théorie des jeux inexistants dans Mathlib ; doit se rabattre sur l'analyse par cas.
  - Cible D (pd_defect_is_pure_ne) : P2 — preuve multi-étapes requérant des
    disjonctions de cas Fin 2 et des comparaisons Int.

  ---
  English:
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

/-! ## Définitions de théorie des jeux (autonomes)

English: Game Theory Definitions (self-contained) -/

/-- Un jeu 2×2 : 2 joueurs, 2 actions chacun.
    English: A 2x2 game: 2 players, 2 actions each. -/
structure Game2x2 where
  payoff1 : Fin 2 → Fin 2 → Int
  payoff2 : Fin 2 → Fin 2 → Int

/-- L'action a domine strictement l'action a' pour le joueur 1.
    English: Action a strictly dominates action a' for player 1. -/
def strictlyDominates1 (g : Game2x2) (a a' : Fin 2) : Prop :=
  ∀ a2 : Fin 2, g.payoff1 a a2 > g.payoff1 a' a2

/-- Équilibre de Nash en stratégies pures pour les jeux 2×2.
    English: Nash equilibrium in pure strategies for 2x2 games. -/
def isPureNashEquilibrium (g : Game2x2) (a1 : Fin 2) (a2 : Fin 2) : Prop :=
  (∀ a1' : Fin 2, g.payoff1 a1 a2 ≥ g.payoff1 a1' a2) ∧
  (∀ a2' : Fin 2, g.payoff2 a1 a2 ≥ g.payoff2 a1 a2')

/-! ## Dilemme du prisonnier

English: Prisoner's Dilemma -/

/-- Dilemme du prisonnier : C=0 (Coopérer), D=1 (Trahir).
    English: Prisoner's Dilemma: C=0 (Cooperate), D=1 (Defect). -/
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

/-! ## Cibles de calibration

English: Calibration Targets -/

/-- Cible C (P3) : dominance stricte de la trahison dans le dilemme du prisonnier.
    Exerce P3 : l'agent peut chercher dans Mathlib des lemmes de théorie des jeux inexistants.
    Approche correcte : unfold + disjonction de cas Fin 2 + arithmétique.
    Itérations attendues : 3-5 (recherche → échec → repli → disjonction de cas → fermer).

    English: Target C (P3): Strict dominance of defection in Prisoner's Dilemma.
    Exercises P3: agent may search Mathlib for game-theory lemmas that don't exist.
    Correct approach: unfold + Fin 2 case split + arithmetic.
    Expected iterations: 3-5 (search → fail → fallback → case split → close). -/
theorem strictly_domin_defect_pd :
    strictlyDominates1 prisonersDilemma Trahir Cooperer := by
  unfold strictlyDominates1; intro a2; fin_cases a2 <;> decide

/-- Cible D (P2) : (D, D) est un équilibre de Nash pur du dilemme du prisonnier.
    Exerce P2 : requiert une analyse de cas Fin 2 + comparaison Int pour les deux joueurs.
    Itérations attendues : 4-7 (unfold → disjonction de cas → arithmétique → fermer).

    English: Target D (P2): (D, D) is a pure Nash equilibrium of Prisoner's Dilemma.
    Exercises P2: requires Fin 2 case analysis + Int comparison across both players.
    Expected iterations: 4-7 (unfold → case split → arithmetic → close). -/
theorem pd_defect_is_pure_ne :
    isPureNashEquilibrium prisonersDilemma Trahir Trahir := by
  unfold isPureNashEquilibrium
  constructor <;> intro a <;> fin_cases a <;> norm_num [prisonersDilemma, Trahir]

/-- Cible E (P1+P2) : (C, C) n'est PAS un équilibre de Nash pur.
    Plus difficile : requiert de construire un contre-exemple (trahir bat coopérer).
    Cela exerce la capacité du prouveur à démontrer des énoncés NÉGATIFS.
    Itérations attendues : 5-10 (unfold → négation → construire le témoin → decide).

    English: Target E (P1+P2): (C, C) is NOT a pure Nash equilibrium.
    Harder: requires constructing a counterexample (defect beats cooperate).
    This exercises the prover's ability to prove NEGATIVE statements.
    Expected iterations: 5-10 (unfold → negation → construct witness → decide). -/
theorem pd_cooperate_not_ne :
    ¬ isPureNashEquilibrium prisonersDilemma Cooperer Cooperer := by
  unfold Not
  intro h
  rcases h with ⟨h1, h2⟩
  have hdev := h1 Trahir
  norm_num [isPureNashEquilibrium, prisonersDilemma, Cooperer, Trahir] at hdev

/-! ## Cible de calibration à augmentation de sorry (P4)

English: Sorry-Increase Calibration Target (P4) -/

/-- Cible F (P4) : cas d'augmentation de sorry — le harnais ne DOIT PAS revert quand le
    compte de sorry augmente mais que le build passe. Cette cible est CONÇUE pour que le
    prouveur décompose naturellement la preuve en deux sous-buts (la contrainte d'incitation
    de chaque joueur).

    Le prouveur devrait produire quelque chose comme :
      constructor
      · sorry  -- le joueur 1 n'a aucune incitation à dévier
      · sorry  -- le joueur 2 n'a aucune incitation à dévier
    Ce qui augmente sorry 1→2 mais compile. Le harnais doit préserver cela.

    Itérations attendues : 3-5 (unfold → constructor → 2 sorries → prouver l'un peut-être).

    English: Target F (P4): sorry-increase case — harness must NOT revert when sorry count
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
  exact pd_defect_is_pure_ne

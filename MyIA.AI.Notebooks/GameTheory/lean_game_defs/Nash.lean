/-
  Définitions de l'équilibre de Nash en Lean 4
  ============================================

  Définit l'équilibre de Nash et les notions associées :
  - Meilleure réponse
  - Équilibre de Nash en stratégies pures
  - Équilibre de Nash en stratégies mixtes
  - Dominance stricte

  Basé sur GameTheory-16-Lean-Definitions.ipynb

  ---
  English:
  Nash Equilibrium Definitions in Lean 4
  ======================================

  Defines Nash equilibrium and related concepts:
  - Best response
  - Pure Nash equilibrium
  - Mixed Nash equilibrium
  - Strict dominance

  Based on GameTheory-16-Lean-Definitions.ipynb
-/

import Basic

/-!
## Meilleure réponse

---
English:
## Best Response
-/

/-- Le joueur 1 joue une meilleure réponse face à `s2`.
    English: Player 1 plays a best response to s2 -/
def isBestResponse1 (g : Game2x2) (s1 : Fin 2 → Float) (s2 : Fin 2 → Float) : Prop :=
  ∀ s1' : Fin 2 → Float,
    expectedPayoff1 g s1 s2 >= expectedPayoff1 g s1' s2

/-- Le joueur 2 joue une meilleure réponse face à `s1`.
    English: Player 2 plays a best response to s1 -/
def isBestResponse2 (g : Game2x2) (s1 : Fin 2 → Float) (s2 : Fin 2 → Float) : Prop :=
  ∀ s2' : Fin 2 → Float,
    expectedPayoff2 g s1 s2 >= expectedPayoff2 g s1 s2'

/-!
## Équilibre de Nash

---
English:
## Nash Equilibrium
-/

/-- Équilibre de Nash en stratégies mixtes : chaque joueur joue une meilleure réponse.
    English: Nash equilibrium in mixed strategies: each player plays a best response -/
def isNashEquilibrium (g : Game2x2) (s1 : Fin 2 → Float) (s2 : Fin 2 → Float) : Prop :=
  isBestResponse1 g s1 s2 ∧ isBestResponse2 g s1 s2

/-- Équilibre de Nash en stratégies pures pour les jeux 2x2.
    English: Nash equilibrium in pure strategies for 2x2 games -/
def isPureNashEquilibrium (g : Game2x2) (a1 : Fin 2) (a2 : Fin 2) : Prop :=
  -- Le joueur 1 ne peut pas améliorer en changeant d'action
  (∀ a1' : Fin 2, g.payoff1 a1 a2 >= g.payoff1 a1' a2) ∧
  -- Le joueur 2 ne peut pas améliorer en changeant d'action
  (∀ a2' : Fin 2, g.payoff2 a1 a2 >= g.payoff2 a1 a2')

/-!
## Dominance

---
English:
## Dominance
-/

/-- L'action `a` domine strictement l'action `a'` pour le joueur 1.
    English: Action a strictly dominates action a' for player 1 -/
def strictlyDominates1 (g : Game2x2) (a a' : Fin 2) : Prop :=
  ∀ a2 : Fin 2, g.payoff1 a a2 > g.payoff1 a' a2

/-- L'action `a` domine faiblement l'action `a'` pour le joueur 1.
    English: Action a weakly dominates action a' for player 1 -/
def weaklyDominates1 (g : Game2x2) (a a' : Fin 2) : Prop :=
  (∀ a2 : Fin 2, g.payoff1 a a2 >= g.payoff1 a' a2) ∧
  (∃ a2 : Fin 2, g.payoff1 a a2 > g.payoff1 a' a2)

/-- L'action `a` domine strictement l'action `a'` pour le joueur 2.
    English: Action a strictly dominates action a' for player 2 -/
def strictlyDominates2 (g : Game2x2) (a a' : Fin 2) : Prop :=
  ∀ a1 : Fin 2, g.payoff2 a1 a > g.payoff2 a1 a'

/-!
## Jeux classiques

---
English:
## Classic Games
-/

/-- Dilemme du prisonnier : C=0 (Coopérer), D=1 (Trahir).
    English: Prisoner's Dilemma: C=0 (Cooperate), D=1 (Defect) -/
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

/-- Jeu de la poule (Chicken) : Céder=0, Foncer=1.
    English: Chicken Game: Yield=0, Charge=1 -/
def chickenGame : Game2x2 := {
  payoff1 := fun i j =>
    match i.val, j.val with
    | 0, 0 => 3  -- (Yield, Yield)
    | 0, 1 => 2  -- (Yield, Charge)
    | 1, 0 => 4  -- (Charge, Yield)
    | 1, 1 => 0  -- (Charge, Charge) - collision !
    | _, _ => 0
  payoff2 := fun i j =>
    match i.val, j.val with
    | 0, 0 => 3
    | 0, 1 => 4
    | 1, 0 => 2
    | 1, 1 => 0
    | _, _ => 0
}

/-- Chasse au cerf (Stag Hunt) : Cerf=0, Lièvre=1.
    English: Stag Hunt: Stag=0, Hare=1 -/
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

/-- Matching Pennies (jeu à somme nulle) : Pile=0, Face=1.
    English: Matching Pennies (zero-sum): Heads=0, Tails=1 -/
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

/-!
## Noms d'actions

---
English:
## Action Names
-/

def Cooperer : Fin 2 := ⟨0, by omega⟩
def Trahir : Fin 2 := ⟨1, by omega⟩
def Ceder : Fin 2 := ⟨0, by omega⟩
def Foncer : Fin 2 := ⟨1, by omega⟩
def Cerf : Fin 2 := ⟨0, by omega⟩
def Lievre : Fin 2 := ⟨1, by omega⟩
def Pile : Fin 2 := ⟨0, by omega⟩
def Face : Fin 2 := ⟨1, by omega⟩

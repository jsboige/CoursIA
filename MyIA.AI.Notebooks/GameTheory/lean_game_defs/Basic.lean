/-
  Définitions fondamentales de la théorie des jeux en Lean 4
  ==========================================================

  Définit les structures fondamentales des jeux sous forme normale :
  - NormalFormGame : structure générale de jeu
  - FiniteGame : jeux à joueurs et actions en nombre fini
  - Game2x2 : jeux spécialisés à 2 joueurs et 2 actions

  Basé sur GameTheory-16-Lean-Definitions.ipynb

  ---
  English:
  Basic Game Theory Definitions in Lean 4
  ========================================

  Defines fundamental structures for normal-form games:
  - NormalFormGame: General game structure
  - FiniteGame: Games with finite players and actions
  - Game2x2: Specialized 2-player, 2-action games

  Based on GameTheory-16-Lean-Definitions.ipynb
-/

/-!
## Jeu sous forme normale

---
English:
## Normal Form Game
-/

/-- Un jeu sous forme normale avec des ensembles arbitraires de joueurs et d'actions.
    English: A normal-form game with arbitrary player and action sets -/
structure NormalFormGame where
  /-- Ensemble des joueurs.
      English: Set of players -/
  Players : Type
  /-- Ensemble des actions pour chaque joueur.
      English: Set of actions for each player -/
  Actions : Players → Type
  /-- Fonction de paiement pour chaque joueur.
      English: Payoff function for each player -/
  payoff : (i : Players) → ((j : Players) → Actions j) → Int

/-!
## Jeu fini

---
English:
## Finite Game
-/

/-- Un jeu fini où les joueurs et les actions sont indexés par des types `Fin`.
    English: A finite game where players and actions are indexed by Fin types -/
structure FiniteGame where
  /-- Nombre de joueurs (utilise `Fin n` pour avoir exactement n joueurs).
      English: Number of players (uses Fin n to have exactly n players) -/
  numPlayers : Nat
  /-- Nombre d'actions pour chaque joueur.
      English: Number of actions for each player -/
  numActions : Fin numPlayers → Nat
  /-- Fonction de paiement : pour chaque joueur, renvoie le paiement étant donné le profil d'actions.
      English: Payoff function: for each player, returns the payoff given action profile -/
  payoff : (i : Fin numPlayers) → ((j : Fin numPlayers) → Fin (numActions j)) → Int

/-!
## Jeux 2x2

---
English:
## 2x2 Games
-/

/-- Un jeu 2x2 : 2 joueurs, 2 actions chacun.
    English: A 2x2 game: 2 players, 2 actions each -/
structure Game2x2 where
  /-- Matrice de paiement du joueur 1 (lignes).
      English: Player 1's payoff matrix (rows) -/
  payoff1 : Fin 2 → Fin 2 → Int
  /-- Matrice de paiement du joueur 2 (colonnes).
      English: Player 2's payoff matrix (columns) -/
  payoff2 : Fin 2 → Fin 2 → Int

/-- Construit un jeu 2x2 à partir de 8 valeurs de paiement.
    English: Create a 2x2 game from 8 payoff values -/
def mkGame2x2 (a11 b11 a12 b12 a21 b21 a22 b22 : Int) : Game2x2 := {
  payoff1 := fun i j =>
    match i.val, j.val with
    | 0, 0 => a11 | 0, 1 => a12
    | 1, 0 => a21 | 1, 1 => a22
    | _, _ => 0
  payoff2 := fun i j =>
    match i.val, j.val with
    | 0, 0 => b11 | 0, 1 => b12
    | 1, 0 => b21 | 1, 1 => b22
    | _, _ => 0
}

/-!
## Stratégies

---
English:
## Strategies
-/

/-- Une stratégie pure est simplement une action.
    English: A pure strategy is just an action -/
def PureStrategy (g : FiniteGame) (i : Fin g.numPlayers) := Fin (g.numActions i)

/-- Un profil de stratégies pures : une stratégie par joueur.
    English: A profile of pure strategies: one strategy per player -/
def PureStrategyProfile (g : FiniteGame) := (i : Fin g.numPlayers) → Fin (g.numActions i)

/-!
## Stratégies mixtes (version simplifiée)

---
English:
## Mixed Strategies (simplified)
-/

/-- Vérifie si une fonction associe des valeurs non négatives.
    English: Check if a function assigns non-negative values -/
def isNonNeg (f : Fin n → Float) : Prop := ∀ i, f i >= 0

/-- Vérifie si les probabilités somment à un.
    English: Check if probabilities sum to one -/
def sumToOne (f : Fin n → Float) : Prop :=
  (List.finRange n).foldl (fun acc i => acc + f i) 0 = 1

/-- Profil de stratégies mixtes pour les jeux à 2 joueurs.
    English: Mixed strategy profile for 2-player games -/
structure MixedProfile2 (n1 n2 : Nat) where
  sigma1 : Fin n1 → Float
  sigma2 : Fin n2 → Float
  h1_pos : ∀ i, sigma1 i >= 0 := by decide
  h2_pos : ∀ i, sigma2 i >= 0 := by decide

/-!
## Paiements espérés

---
English:
## Expected Payoffs
-/

/-- Convertit un `Int` en `Float`.
    English: Convert Int to Float -/
def intToFloat (n : Int) : Float := Float.ofInt n

/-- Paiement espéré du joueur 1 dans un jeu 2x2.
    English: Expected payoff for player 1 in a 2x2 game -/
def expectedPayoff1 (g : Game2x2) (s1 : Fin 2 → Float) (s2 : Fin 2 → Float) : Float :=
  let i0 : Fin 2 := ⟨0, by omega⟩
  let i1 : Fin 2 := ⟨1, by omega⟩
  s1 i0 * s2 i0 * intToFloat (g.payoff1 i0 i0) +
  s1 i0 * s2 i1 * intToFloat (g.payoff1 i0 i1) +
  s1 i1 * s2 i0 * intToFloat (g.payoff1 i1 i0) +
  s1 i1 * s2 i1 * intToFloat (g.payoff1 i1 i1)

/-- Paiement espéré du joueur 2 dans un jeu 2x2.
    English: Expected payoff for player 2 in a 2x2 game -/
def expectedPayoff2 (g : Game2x2) (s1 : Fin 2 → Float) (s2 : Fin 2 → Float) : Float :=
  let i0 : Fin 2 := ⟨0, by omega⟩
  let i1 : Fin 2 := ⟨1, by omega⟩
  s1 i0 * s2 i0 * intToFloat (g.payoff2 i0 i0) +
  s1 i0 * s2 i1 * intToFloat (g.payoff2 i0 i1) +
  s1 i1 * s2 i0 * intToFloat (g.payoff2 i1 i0) +
  s1 i1 * s2 i1 * intToFloat (g.payoff2 i1 i1)

/-- Convertit une stratégie pure en une stratégie mixte dégénérée.
    English: Convert a pure strategy to a degenerate mixed strategy -/
def pureToMixed (a : Fin 2) : Fin 2 → Float :=
  fun i => if i == a then 1.0 else 0.0

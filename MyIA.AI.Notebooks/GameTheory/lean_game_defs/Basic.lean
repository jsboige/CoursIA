/-
  Basic Game Theory Definitions in Lean 4
  ========================================

  Defines fundamental structures for normal-form games:
  - NormalFormGame: General game structure
  - FiniteGame: Games with finite players and actions
  - Game2x2: Specialized 2-player, 2-action games

  Based on GameTheory-16-Lean-Definitions.ipynb
-/

/-! ## Normal Form Game -/

/-- A normal-form game with arbitrary player and action sets -/
structure NormalFormGame where
  /-- Set of players -/
  Players : Type
  /-- Set of actions for each player -/
  Actions : Players → Type
  /-- Payoff function for each player -/
  payoff : (i : Players) → ((j : Players) → Actions j) → Int

/-! ## Finite Game -/

/-- A finite game where players and actions are indexed by Fin types -/
structure FiniteGame where
  /-- Number of players (uses Fin n to have exactly n players) -/
  numPlayers : Nat
  /-- Number of actions for each player -/
  numActions : Fin numPlayers → Nat
  /-- Payoff function: for each player, returns the payoff given action profile -/
  payoff : (i : Fin numPlayers) → ((j : Fin numPlayers) → Fin (numActions j)) → Int

/-! ## 2x2 Games -/

/-- A 2x2 game: 2 players, 2 actions each -/
structure Game2x2 where
  /-- Player 1's payoff matrix (rows) -/
  payoff1 : Fin 2 → Fin 2 → Int
  /-- Player 2's payoff matrix (columns) -/
  payoff2 : Fin 2 → Fin 2 → Int

/-- Create a 2x2 game from 8 payoff values -/
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

/-! ## Strategies -/

/-- A pure strategy is just an action -/
def PureStrategy (g : FiniteGame) (i : Fin g.numPlayers) := Fin (g.numActions i)

/-- A profile of pure strategies: one strategy per player -/
def PureStrategyProfile (g : FiniteGame) := (i : Fin g.numPlayers) → Fin (g.numActions i)

/-! ## Mixed Strategies (simplified) -/

/-- Check if a function assigns non-negative values -/
def isNonNeg (f : Fin n → Float) : Prop := ∀ i, f i >= 0

/-- Check if probabilities sum to one -/
def sumToOne (f : Fin n → Float) : Prop :=
  (List.finRange n).foldl (fun acc i => acc + f i) 0 = 1

/-- Mixed strategy profile for 2-player games -/
structure MixedProfile2 (n1 n2 : Nat) where
  sigma1 : Fin n1 → Float
  sigma2 : Fin n2 → Float
  h1_pos : ∀ i, sigma1 i >= 0 := by decide
  h2_pos : ∀ i, sigma2 i >= 0 := by decide

/-! ## Expected Payoffs -/

/-- Convert Int to Float -/
def intToFloat (n : Int) : Float := Float.ofInt n

/-- Expected payoff for player 1 in a 2x2 game -/
def expectedPayoff1 (g : Game2x2) (s1 : Fin 2 → Float) (s2 : Fin 2 → Float) : Float :=
  let i0 : Fin 2 := ⟨0, by omega⟩
  let i1 : Fin 2 := ⟨1, by omega⟩
  s1 i0 * s2 i0 * intToFloat (g.payoff1 i0 i0) +
  s1 i0 * s2 i1 * intToFloat (g.payoff1 i0 i1) +
  s1 i1 * s2 i0 * intToFloat (g.payoff1 i1 i0) +
  s1 i1 * s2 i1 * intToFloat (g.payoff1 i1 i1)

/-- Expected payoff for player 2 in a 2x2 game -/
def expectedPayoff2 (g : Game2x2) (s1 : Fin 2 → Float) (s2 : Fin 2 → Float) : Float :=
  let i0 : Fin 2 := ⟨0, by omega⟩
  let i1 : Fin 2 := ⟨1, by omega⟩
  s1 i0 * s2 i0 * intToFloat (g.payoff2 i0 i0) +
  s1 i0 * s2 i1 * intToFloat (g.payoff2 i0 i1) +
  s1 i1 * s2 i0 * intToFloat (g.payoff2 i1 i0) +
  s1 i1 * s2 i1 * intToFloat (g.payoff2 i1 i1)

/-- Convert a pure strategy to a degenerate mixed strategy -/
def pureToMixed (a : Fin 2) : Fin 2 → Float :=
  fun i => if i == a then 1.0 else 0.0

/-
  Combinatorial Game Theory in Lean 4
  ====================================

  Introduces concepts for combinatorial games:
  - Two-player sequential games
  - Perfect information
  - Zero-sum games
  - Win/Loss determination

  Note: For full PGame support, use Mathlib:
  import Mathlib.SetTheory.PGame.Basic
  import Mathlib.SetTheory.Game.Nim

  Based on GameTheory-18-Lean-CombinatorialGames.ipynb
-/

/-! ## Simple Combinatorial Game Structures -/

/-- A simple game tree node -/
inductive GameTree where
  | leaf : (winner : Int) → GameTree  -- 1 = player 1 wins, -1 = player 2 wins, 0 = draw
  | node : (moves : List GameTree) → GameTree

/-- Evaluate a game tree using minimax (player 1 = maximizer) -/
def minimax : GameTree → Bool → Int
  | GameTree.leaf w, _ => w
  | GameTree.node [], _ => 0  -- No moves = draw
  | GameTree.node (m :: ms), isMax =>
    let first := minimax m (not isMax)
    let rest := minimax (GameTree.node ms) isMax
    if isMax then max first rest else min first rest

/-! ## Nim-like Games -/

/-- A Nim heap is just a natural number -/
def NimHeap := Nat

/-- A Nim position is a list of heaps -/
def NimPosition := List Nat

/-- XOR of all heap sizes (Sprague-Grundy value for Nim) -/
def nimSum (pos : NimPosition) : Nat :=
  pos.foldl (· ^^^ ·) 0

/-- A Nim position is winning for the player to move iff nimSum ≠ 0 -/
def isWinningNim (pos : NimPosition) : Bool :=
  nimSum pos != 0

/-- Get all valid moves from a Nim position -/
def nimMoves (pos : NimPosition) : List NimPosition :=
  pos.enum.bind fun (i, heap) =>
    (List.range heap).map fun newSize =>
      pos.set i newSize

/-! ## Two-Player Perfect Information Game -/

/-- A two-player perfect information game -/
structure TwoPlayerGame (State : Type) where
  /-- Initial state -/
  initial : State
  /-- Check if it's player 1's turn -/
  isPlayer1Turn : State → Bool
  /-- Get available moves -/
  moves : State → List State
  /-- Check if game is over -/
  isTerminal : State → Bool
  /-- Get winner (1 = P1, -1 = P2, 0 = draw) -/
  winner : State → Int

/-- Check if a state is winning for the current player using backward induction -/
partial def isWinning {State : Type} (game : TwoPlayerGame State) (state : State) : Bool :=
  if game.isTerminal state then
    let w := game.winner state
    if game.isPlayer1Turn state then w > 0 else w < 0
  else
    let nextStates := game.moves state
    if nextStates.isEmpty then false
    else nextStates.any fun s => not (isWinning game s)

/-! ## Nim as a TwoPlayerGame -/

/-- Nim game instance -/
def nimGame : TwoPlayerGame NimPosition := {
  initial := [3, 4, 5]  -- Classic starting position
  isPlayer1Turn := fun pos => (pos.foldl (· + ·) 0) % 2 == 1  -- Simplified
  moves := nimMoves
  isTerminal := fun pos => pos.all (· == 0)
  winner := fun pos => if pos.all (· == 0) then -1 else 0  -- Last to move loses
}

/-! ## Sprague-Grundy Theorem (Statement) -/

/-- The Sprague-Grundy value of a game position -/
-- For impartial games, every position is equivalent to a Nim heap of some size
-- This is a simplified version; full implementation requires more machinery

/-- Minimum excludant (mex) of a set of naturals -/
def mex (s : List Nat) : Nat :=
  let sorted := s.eraseDups.mergeSort (· < ·)
  match sorted.find? fun n => !sorted.contains n with
  | some n => n
  | none => sorted.length

/-- Compute Grundy value for a simple game -/
-- grundy(terminal) = 0
-- grundy(pos) = mex { grundy(pos') : pos' in moves(pos) }
partial def grundyValue {State : Type} [BEq State] [Hashable State]
    (moves : State → List State) (isTerminal : State → Bool) (state : State) : Nat :=
  if isTerminal state then 0
  else
    let childValues := (moves state).map (grundyValue moves isTerminal)
    mex childValues

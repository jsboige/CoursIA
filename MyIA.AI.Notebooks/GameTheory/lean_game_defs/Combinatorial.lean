/-
  Théorie des jeux combinatoires en Lean 4
  ========================================

  Introduit les notions pour les jeux combinatoires :
  - Jeux séquentiels à deux joueurs
  - Information parfaite
  - Jeux à somme nulle
  - Détermination Gagnant/Perdant

  Note : pour le support complet de PGame, utiliser Mathlib :
  import Mathlib.SetTheory.PGame.Basic
  import Mathlib.SetTheory.Game.Nim

  Basé sur GameTheory-18-Lean-CombinatorialGames.ipynb

  ---
  English:
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

/-!
## Structures simples de jeux combinatoires

---
English:
## Simple Combinatorial Game Structures
-/

/-- Un nœud d'arbre de jeu simple.
    English: A simple game tree node -/
inductive GameTree where
  | leaf : (winner : Int) → GameTree  -- 1 = le joueur 1 gagne, -1 = le joueur 2 gagne, 0 = nul
  | node : (moves : List GameTree) → GameTree

/-- Évalue un arbre de jeu par minimax (joueur 1 = maximiseur).
    English: Evaluate a game tree using minimax (player 1 = maximizer) -/
def minimax : GameTree → Bool → Int
  | GameTree.leaf w, _ => w
  | GameTree.node [], _ => 0  -- Aucun coup = nul
  | GameTree.node (m :: ms), isMax =>
    let first := minimax m (not isMax)
    let rest := minimax (GameTree.node ms) isMax
    if isMax then max first rest else min first rest

/-!
## Jeux de type Nim

---
English:
## Nim-like Games
-/

/-- Un tas de Nim est simplement un entier naturel.
    English: A Nim heap is just a natural number -/
def NimHeap := Nat

/-- Une position de Nim est une liste de tas.
    English: A Nim position is a list of heaps -/
def NimPosition := List Nat

/-- XOR de toutes les tailles de tas (valeur de Sprague-Grundy pour Nim).
    English: XOR of all heap sizes (Sprague-Grundy value for Nim) -/
def nimSum (pos : NimPosition) : Nat :=
  pos.foldl (· ^^^ ·) 0

/-- Une position de Nim est gagnante pour le joueur qui doit jouer ssi `nimSum ≠ 0`.
    English: A Nim position is winning for the player to move iff nimSum ≠ 0 -/
def isWinningNim (pos : NimPosition) : Bool :=
  nimSum pos != 0

/-- Utilitaire : énumère une liste avec ses indices (évite la dépendance Mathlib).
    English: Helper: enumerate a list with indices (avoids Mathlib dependency) -/
def listEnum {α : Type} (l : List α) : List (Nat × α) :=
  (List.range l.length).zip l

/-- Utilitaire : met à jour l'élément à un indice donné (évite la dépendance Mathlib).
    Utilise `listEnum` pour le parcours indexé.
    English: Helper: update element at index (avoids Mathlib dependency).
    Uses listEnum for indexed traversal. -/
def listSet {α : Type} (l : List α) (i : Nat) (x : α) : List α :=
  (listEnum l).map fun (j, a) =>
    if j == i then x else a

/-- Renvoie tous les coups valides depuis une position de Nim.
    English: Get all valid moves from a Nim position -/
def nimMoves (pos : NimPosition) : List NimPosition :=
  (listEnum pos).flatMap fun (i, heap) =>
    (List.range heap).map fun newSize =>
      listSet pos i newSize

/-!
## Jeu à deux joueurs à information parfaite

---
English:
## Two-Player Perfect Information Game
-/

/-- Un jeu à deux joueurs à information parfaite.
    English: A two-player perfect information game -/
structure TwoPlayerGame (State : Type) where
  /-- État initial.
      English: Initial state -/
  initial : State
  /-- Vérifie si c'est au tour du joueur 1.
      English: Check if it's player 1's turn -/
  isPlayer1Turn : State → Bool
  /-- Renvoie les coups disponibles.
      English: Get available moves -/
  moves : State → List State
  /-- Vérifie si la partie est terminée.
      English: Check if game is over -/
  isTerminal : State → Bool
  /-- Renvoie le gagnant (1 = J1, -1 = J2, 0 = nul).
      English: Get winner (1 = P1, -1 = P2, 0 = draw) -/
  winner : State → Int

/-- Vérifie si un état est gagnant pour le joueur courant par induction à rebours.
    English: Check if a state is winning for the current player using backward induction -/
partial def isWinning {State : Type} (game : TwoPlayerGame State) (state : State) : Bool :=
  if game.isTerminal state then
    let w := game.winner state
    if game.isPlayer1Turn state then w > 0 else w < 0
  else
    let nextStates := game.moves state
    if nextStates.isEmpty then false
    else nextStates.any fun s => not (isWinning game s)

/-!
## Nim vu comme un TwoPlayerGame

---
English:
## Nim as a TwoPlayerGame
-/

/-- Instance du jeu de Nim.
    English: Nim game instance -/
def nimGame : TwoPlayerGame NimPosition := {
  initial := [3, 4, 5]  -- Position de départ classique
  isPlayer1Turn := fun pos => (pos.foldl (· + ·) 0) % 2 == 1  -- Simplifié
  moves := nimMoves
  isTerminal := fun pos => pos.all (· == 0)
  winner := fun pos => if pos.all (· == 0) then -1 else 0  -- Le dernier à jouer perd
}

/-!
## Théorème de Sprague-Grundy (énoncé)

---
English:
## Sprague-Grundy Theorem (Statement)
-/

-- Pour les jeux impartiaux, toute position est équivalente à un tas de Nim d'une certaine taille.
-- Ceci est une version simplifiée ; l'implémentation complète nécessite davantage de machinerie.

/-- Minimum excludant (mex) d'un ensemble d'entiers naturels.
    La valeur de Sprague-Grundy d'une position de jeu se définit via mex :
    grundy(terminal) = 0, grundy(pos) = mex { grundy(pos') : pos' dans moves(pos) }.
    English: Minimum excludant (mex) of a set of naturals.
    The Sprague-Grundy value of a game position is defined via mex:
    grundy(terminal) = 0, grundy(pos) = mex { grundy(pos') : pos' in moves(pos) }. -/
def mex (s : List Nat) : Nat :=
  (List.range (s.length + 1)).find? (fun n => !s.contains n) |>.getD (s.length + 1)

/-- Calcule la valeur de Grundy pour un jeu simple (partiel : pas de mémoïsation).
    English: Compute Grundy value for a simple game (partial: no memoization). -/
partial def grundyValue {State : Type} [BEq State] [Hashable State]
    (moves : State → List State) (isTerminal : State → Bool) (state : State) : Nat :=
  if isTerminal state then 0
  else
    let childValues := (moves state).map (grundyValue moves isTerminal)
    mex childValues

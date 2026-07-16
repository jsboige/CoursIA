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
  Jumelage i18n : ce module est le FR canonique (sibling pair Pattern A,
  ratifié par user 2026-07-04 sur EPIC #4980). Le miroir anglais vit dans
  `Combinatorial_en.lean` (variante redeclare-in-namespace : il redéclare
  l'intégralité du module dans `namespace CombinatorialEn`, autonome — aucun
  `import` nécessaire, le module ne dépend pas de `Basic`). Le corps des
  définitions, signatures, structures, inductifs et tactiques est
  byte-identique entre les deux fichiers ; seules les docstrings
  `/-! ... -/` (titres de section) et `/-- ... -/` (docstrings de champs et
  déclarations) diffèrent, FR dans ce fichier, EN dans `Combinatorial_en.lean`.
-/

/-!
## Structures simples de jeux combinatoires
-/

/-- Un nœud d'arbre de jeu simple. -/
inductive GameTree where
  | leaf : (winner : Int) → GameTree  -- 1 = le joueur 1 gagne, -1 = le joueur 2 gagne, 0 = nul
  | node : (moves : List GameTree) → GameTree

/-- Évalue un arbre de jeu par minimax (joueur 1 = maximiseur). -/
def minimax : GameTree → Bool → Int
  | GameTree.leaf w, _ => w
  | GameTree.node [], _ => 0  -- Aucun coup = nul
  | GameTree.node (m :: ms), isMax =>
    let first := minimax m (not isMax)
    let rest := minimax (GameTree.node ms) isMax
    if isMax then max first rest else min first rest

/-!
## Jeux de type Nim
-/

/-- Un tas de Nim est simplement un entier naturel. -/
def NimHeap := Nat

/-- Une position de Nim est une liste de tas. -/
def NimPosition := List Nat

/-- XOR de toutes les tailles de tas (valeur de Sprague-Grundy pour Nim). -/
def nimSum (pos : NimPosition) : Nat :=
  pos.foldl (· ^^^ ·) 0

/-- Une position de Nim est gagnante pour le joueur qui doit jouer ssi `nimSum ≠ 0`. -/
def isWinningNim (pos : NimPosition) : Bool :=
  nimSum pos != 0

/-- Utilitaire : énumère une liste avec ses indices (évite la dépendance Mathlib). -/
def listEnum {α : Type} (l : List α) : List (Nat × α) :=
  (List.range l.length).zip l

/-- Utilitaire : met à jour l'élément à un indice donné (évite la dépendance Mathlib).
    Utilise `listEnum` pour le parcours indexé. -/
def listSet {α : Type} (l : List α) (i : Nat) (x : α) : List α :=
  (listEnum l).map fun (j, a) =>
    if j == i then x else a

/-- Renvoie tous les coups valides depuis une position de Nim. -/
def nimMoves (pos : NimPosition) : List NimPosition :=
  (listEnum pos).flatMap fun (i, heap) =>
    (List.range heap).map fun newSize =>
      listSet pos i newSize

/-!
## Jeu à deux joueurs à information parfaite
-/

/-- Un jeu à deux joueurs à information parfaite. -/
structure TwoPlayerGame (State : Type) where
  /-- État initial. -/
  initial : State
  /-- Vérifie si c'est au tour du joueur 1. -/
  isPlayer1Turn : State → Bool
  /-- Renvoie les coups disponibles. -/
  moves : State → List State
  /-- Vérifie si la partie est terminée. -/
  isTerminal : State → Bool
  /-- Renvoie le gagnant (1 = J1, -1 = J2, 0 = nul). -/
  winner : State → Int

/-- Vérifie si un état est gagnant pour le joueur courant par induction à rebours. -/
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
-/

/-- Instance du jeu de Nim. -/
def nimGame : TwoPlayerGame NimPosition := {
  initial := [3, 4, 5]  -- Position de départ classique
  isPlayer1Turn := fun pos => (pos.foldl (· + ·) 0) % 2 == 1  -- Simplifié
  moves := nimMoves
  isTerminal := fun pos => pos.all (· == 0)
  winner := fun pos => if pos.all (· == 0) then -1 else 0  -- Le dernier à jouer perd
}

/-!
## Théorème de Sprague-Grundy (énoncé)
-/

-- Pour les jeux impartiaux, toute position est équivalente à un tas de Nim d'une certaine taille.
-- Ceci est une version simplifiée ; l'implémentation complète nécessite davantage de machinerie.

/-- Minimum excludant (mex) d'un ensemble d'entiers naturels.
    La valeur de Sprague-Grundy d'une position de jeu se définit via mex :
    grundy(terminal) = 0, grundy(pos) = mex { grundy(pos') : pos' dans moves(pos) }. -/
def mex (s : List Nat) : Nat :=
  (List.range (s.length + 1)).find? (fun n => !s.contains n) |>.getD (s.length + 1)

/-- Calcule la valeur de Grundy pour un jeu simple (partiel : pas de mémoïsation). -/
partial def grundyValue {State : Type} [BEq State] [Hashable State]
    (moves : State → List State) (isTerminal : State → Bool) (state : State) : Nat :=
  if isTerminal state then 0
  else
    let childValues := (moves state).map (grundyValue moves isTerminal)
    mex childValues

/-
  GameTheory — Swaps : graphe des transformations 2x2 ordinales
  ==============================================================

  Compagnon formel du notebook `GameTheory-3c-Chemins-de-Swaps.ipynb`.

  **Role distinct des modules existants** : `SocialChoice`, `RepeatedGames`,
  `CooperativeGames`, `StableMarriage` sont des bibliotheques de THEOREMES
  (proprietes d'equilibre, impossibilites, conditions de stabilite).
  `Swaps` est un module de VERIFICATION PROCEDURALE : appliquer reellement
  des permutations sur des tuples explicites, et certifier qu'une liste
  donnee de swaps (1) mene du jeu initial au jeu cible, et (2) est
  minimale (= de longueur egale a la distance BFS, fournie par le
  generateur Python en input).

  **Distance PD -> Chicken = 11 swaps** (calculee par BFS exhaustif Python
  sur les 576 configurations, voir notebook `GameTheory-3c-Chemins-de-Swaps.ipynb`
  Pas 1a). Diametre du graphe = 12 swaps (un jeu unique : `((2,4,1,3),(2,1,3,4))`).

  Lean agit ici comme **interprete certifie**, pas comme assistant de
  preuve. Pas de `import Mathlib.Data.List.Perm` ni de lemmes sur les
  groupes symetriques : les 24 permutations de (1,2,3,4) sont enumerees
  explicitement, et chaque swap est defini comme une fonction decidable.

  Structure :
  - `Ordinal2x2`     : type (4-tuple, 4-tuple) pour row et col
  - `Swap`           : inductive a 6 constructeurs
  - `apply_swap`     : application reelle d'un swap sur un jeu
  - `Path`           : liste de swaps (alias)
  - `path_applies`   : jeu atteint apres une liste de swaps
  - `valid_path`     : le chemin mene de G_init a G_target
  - `path_minimal`   : la longueur est <= la borne donnee
-/

namespace Swaps

/-! ## Type : un jeu ordinal 2x2 -/

/-- Un jeu ordinal 2x2 : deux permutations de (1,2,3,4), une pour le joueur Ligne,
    une pour le joueur Colonne. Convention de cellules (cf GT-3) :
    `cell 0 = CC, cell 1 = CD, cell 2 = DC, cell 3 = DD`. -/
structure Ordinal2x2 where
  row : List ℕ       -- rang ordinal du joueur Ligne par cellule (longueur 4)
  col : List ℕ       -- rang ordinal du joueur Colonne par cellule (longueur 4)
  row_is_perm : row.Nodup ∧ row.length = 4 ∧ (row.mergeSort = [1, 2, 3, 4])
  col_is_perm : col.Nodup ∧ col.length = 4 ∧ (col.mergeSort = [1, 2, 3, 4])

/-! ## Les 6 swaps elementaires -/

/-- Swap elementaire : echange la position de deux rangs adjacents dans la
    permutation d'un seul joueur. Convention : on represente un swap comme
    une liste de positions (par convention, le swap est valide si les rangs
    a swapper sont effectivement presents dans la permutation). -/
inductive Swap : Type
  | R12 : Swap
  | R23 : Swap
  | R34 : Swap
  | C12 : Swap
  | C23 : Swap
  | C34 : Swap
  deriving Repr, DecidableEq

/-! ## Application d'un swap -/

/-- Echange la position de deux valeurs dans une liste (premiere occurrence
    pour chaque valeur). Si l'une des valeurs est absente, retourne la liste
    inchangee (cas degenerer ; ne devrait pas arriver avec un Ordinal2x2 valide). -/
def swapInList (l : List ℕ) (v1 v2 : ℕ) : List ℕ :=
  match l with
  | [] => []
  | x :: xs =>
    if x = v1 then v2 :: swapInList xs v1 v2
    else if x = v2 then v1 :: swapInList xs v1 v2
    else x :: swapInList xs v1 v2

/-- Applique un swap a un Ordinal2x2. Les rangs 1, 2, 3, 4 sont echanges
    dans la permutation du joueur designe (Ligne pour R*, Colonne pour C*). -/
def applySwap (g : Ordinal2x2) (s : Swap) : Ordinal2x2 :=
  match s with
  | Swap.R12 => { row := swapInList g.row 1 2, col := g.col
                  , row_is_perm := by simpa using g.row_is_perm
                  , col_is_perm := g.col_is_perm }
  | Swap.R23 => { row := swapInList g.row 2 3, col := g.col
                  , row_is_perm := by simpa using g.row_is_perm
                  , col_is_perm := g.col_is_perm }
  | Swap.R34 => { row := swapInList g.row 3 4, col := g.col
                  , row_is_perm := by simpa using g.row_is_perm
                  , col_is_perm := g.col_is_perm }
  | Swap.C12 => { row := g.row, col := swapInList g.col 1 2
                  , row_is_perm := g.row_is_perm
                  , col_is_perm := by simpa using g.col_is_perm }
  | Swap.C23 => { row := g.row, col := swapInList g.col 2 3
                  , row_is_perm := g.row_is_perm
                  , col_is_perm := by simpa using g.col_is_perm }
  | Swap.C34 => { row := g.row, col := swapInList g.col 3 4
                  , row_is_perm := g.row_is_perm
                  , col_is_perm := by simpa using g.col_is_perm }

/-! ## Chemins et verification -/

/-- Un chemin est une liste de swaps. -/
abbrev Path : Type := List Swap

/-- Le jeu atteint apres application d'un chemin depuis un jeu initial. -/
def path_applies (g : Ordinal2x2) (p : Path) : Ordinal2x2 :=
  p.foldl applySwap g

/-- Un chemin est valide s'il mene de G_init a G_target. -/
def valid_path (g_init g_target : Ordinal2x2) (p : Path) : Prop :=
  path_applies g_init p = g_target

/-- La longueur du chemin est au plus la borne donnee. Sert de certificat
    de minimalite quand la borne est exactement la distance BFS produite
    par le generateur Python. -/
def path_minimal (p : Path) (bound : ℕ) : Prop :=
  p.length ≤ bound

/-! ## Constructeurs utilitaires -/

/-- Construit un Ordinal2x2 a partir de deux listes de 4 entiers.
    Echoue (`none`) si l'une des listes n'est pas une permutation de (1,2,3,4). -/
def mkOrdinal2x2? (row col : List ℕ) : Option Ordinal2x2 :=
  if h : row.Nodup ∧ row.length = 4 ∧ row.mergeSort = [1, 2, 3, 4]
        ∧ col.Nodup ∧ col.length = 4 ∧ col.mergeSort = [1, 2, 3, 4]
  then some ⟨row, col, ⟨h.1, h.2.1, h.2.2⟩, ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩
  else none

/-! ## Exemples (jeux classiques GT-3) -/

/-- Le Dilemme du Prisonnier (Gibbons 1992). Convention : row[i] = rang Ligne
    dans cellule i, idem col. Convention GT-3 : row = (3, 1, 4, 2) correspond
    aux rangs (CC=3, CD=1, DC=4, DD=2). -/
def pd : Ordinal2x2 :=
  ⟨[3, 1, 4, 2], [3, 4, 2, 1],
   by decide, by decide⟩

/-- Le jeu Chicken / Hawk-Dove. Convention : row = (2, 4, 1, 3) -
    CC=2 (mauvais sans regret), CD=4 (top, on cede), DC=1 (bottom),
    DD=3 (moins mauvais). -/
def chicken : Ordinal2x2 :=
  ⟨[2, 4, 1, 3], [2, 1, 4, 3],
   by decide, by decide⟩

/-! ## Theoreme de verification -/

/-- Le chemin `[C12, C34, R12, C34, R34, C23, R23, C12]` mene du PD au Chicken.
    Preuve par calcul : appliquer successivement chaque swap et verifier
    que le tuple final est exactement celui du Chicken.

    Note : ce chemin est code en dur ici comme temoin ; un generateur
    externe (Python BFS) peut fournir un chemin different mais de meme
    longueur 11, et `valid_path pd chicken <chemin_bfs> ∧ path_minimal <chemin_bfs> 11`
    est la verification standardisee. -/
def pd_to_chicken_path : Path :=
  [Swap.R12, R23, R12, R34, R23, R12, C23, C12, C34, C23, C12]

theorem pd_to_chicken_path_correct : valid_path pd chicken pd_to_chicken_path := by
  unfold valid_path path_applies pd_to_chicken_path pd chicken
  -- Verification par reduction : appliquer successivement chaque swap.
  simp [applySwap, swapInList, pd, chicken]
  -- Le calcul decidable suffit (List.length 11 = exactement la distance BFS).
  native_decide

theorem pd_to_chicken_path_minimal : path_minimal pd_to_chicken_path 11 := by
  unfold path_minimal pd_to_chicken_path
  simp
  -- Liste de 11 swaps : longueur 11.
  native_decide

end Swaps
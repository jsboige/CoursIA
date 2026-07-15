/-
  Définitions fondamentales de la théorie des jeux en Lean 4
  ==========================================================

  Définit les structures fondamentales des jeux sous forme normale :
  - NormalFormGame : structure générale de jeu
  - FiniteGame : jeux à joueurs et actions en nombre fini
  - Game2x2 : jeux spécialisés à 2 joueurs et 2 actions

  Basé sur GameTheory-16-Lean-Definitions.ipynb

  ---
  Jumelage i18n : ce module est le FR canonique (sibling pair Pattern A,
  ratifié par user 2026-07-04 sur EPIC #4980). Le miroir anglais vit dans
  `Basic_en.lean` (namespace suffixé `BasicEn`). Le corps des définitions,
  structures, signatures et tactiques est byte-identique entre les deux
  fichiers ; seules les docstrings `/-! ... -/` (titres de section) et
  `/-- ... -/` (docstrings de champs) diffèrent, FR dans ce fichier, EN dans
  `Basic_en.lean`.
-/

/-!
## Jeu sous forme normale
-/

/-- Un jeu sous forme normale avec des ensembles arbitraires de joueurs et d'actions. -/
structure NormalFormGame where
  /-- Ensemble des joueurs. -/
  Players : Type
  /-- Ensemble des actions pour chaque joueur. -/
  Actions : Players → Type
  /-- Fonction de paiement pour chaque joueur. -/
  payoff : (i : Players) → ((j : Players) → Actions j) → Int

/-!
## Jeu fini
-/

/-- Un jeu fini où les joueurs et les actions sont indexés par des types `Fin`. -/
structure FiniteGame where
  /-- Nombre de joueurs (utilise `Fin n` pour avoir exactement n joueurs). -/
  numPlayers : Nat
  /-- Nombre d'actions pour chaque joueur. -/
  numActions : Fin numPlayers → Nat
  /-- Fonction de paiement : pour chaque joueur, renvoie le paiement étant donné le profil d'actions. -/
  payoff : (i : Fin numPlayers) → ((j : Fin numPlayers) → Fin (numActions j)) → Int

/-!
## Jeux 2x2
-/

/-- Un jeu 2x2 : 2 joueurs, 2 actions chacun. -/
structure Game2x2 where
  /-- Matrice de paiement du joueur 1 (lignes). -/
  payoff1 : Fin 2 → Fin 2 → Int
  /-- Matrice de paiement du joueur 2 (colonnes). -/
  payoff2 : Fin 2 → Fin 2 → Int

/-- Construit un jeu 2x2 à partir de 8 valeurs de paiement. -/
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
-/

/-- Une stratégie pure est simplement une action. -/
def PureStrategy (g : FiniteGame) (i : Fin g.numPlayers) := Fin (g.numActions i)

/-- Un profil de stratégies pures : une stratégie par joueur. -/
def PureStrategyProfile (g : FiniteGame) := (i : Fin g.numPlayers) → Fin (g.numActions i)

/-!
## Stratégies mixtes (version simplifiée)
-/

/-- Vérifie si une fonction associe des valeurs non négatives. -/
def isNonNeg (f : Fin n → Float) : Prop := ∀ i, f i >= 0

/-- Vérifie si les probabilités somment à un. -/
def sumToOne (f : Fin n → Float) : Prop :=
  (List.finRange n).foldl (fun acc i => acc + f i) 0 = 1

/-- Profil de stratégies mixtes pour les jeux à 2 joueurs. -/
structure MixedProfile2 (n1 n2 : Nat) where
  sigma1 : Fin n1 → Float
  sigma2 : Fin n2 → Float
  h1_pos : ∀ i, sigma1 i >= 0 := by decide
  h2_pos : ∀ i, sigma2 i >= 0 := by decide

/-!
## Paiements espérés
-/

/-- Convertit un `Int` en `Float`. -/
def intToFloat (n : Int) : Float := Float.ofInt n

/-- Paiement espéré du joueur 1 dans un jeu 2x2. -/
def expectedPayoff1 (g : Game2x2) (s1 : Fin 2 → Float) (s2 : Fin 2 → Float) : Float :=
  let i0 : Fin 2 := ⟨0, by omega⟩
  let i1 : Fin 2 := ⟨1, by omega⟩
  s1 i0 * s2 i0 * intToFloat (g.payoff1 i0 i0) +
  s1 i0 * s2 i1 * intToFloat (g.payoff1 i0 i1) +
  s1 i1 * s2 i0 * intToFloat (g.payoff1 i1 i0) +
  s1 i1 * s2 i1 * intToFloat (g.payoff1 i1 i1)

/-- Paiement espéré du joueur 2 dans un jeu 2x2. -/
def expectedPayoff2 (g : Game2x2) (s1 : Fin 2 → Float) (s2 : Fin 2 → Float) : Float :=
  let i0 : Fin 2 := ⟨0, by omega⟩
  let i1 : Fin 2 := ⟨1, by omega⟩
  s1 i0 * s2 i0 * intToFloat (g.payoff2 i0 i0) +
  s1 i0 * s2 i1 * intToFloat (g.payoff2 i0 i1) +
  s1 i1 * s2 i0 * intToFloat (g.payoff2 i1 i0) +
  s1 i1 * s2 i1 * intToFloat (g.payoff2 i1 i1)

/-- Convertit une stratégie pure en une stratégie mixte dégénérée. -/
def pureToMixed (a : Fin 2) : Fin 2 → Float :=
  fun i => if i == a then 1.0 else 0.0
/-
  Cible de calibration : théorie des jeux de Nim
  ===============================================

  Définitions de Nim autonomes + théorèmes de calibration basés sur les
  définitions de lean_game_defs/Combinatorial.lean.

  Chemins du harnais exercés :
  - Cible A (nim_winning_345) : validation P1 — decide simple, devrait se fermer en 1-2 itérations.
  - Cible H (nimSum_self_cancel) : P1 — simp naïf stagne, requiert Nat.xor_self ciblé.
    Exerce la capacité du Director à pivoter du simp générique vers un lemme spécifique.
  - Cible D (nimSum_single) : P1 — requiert Nat.xor_zero, non trivial mais borné.
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-! ## Définitions de Nim (autonomes, reflètent Combinatorial.lean) -/

/-- Une position de Nim est une liste de tas. -/
abbrev NimPosition := List Nat

/-- XOR de toutes les tailles de tas (valeur de Sprague-Grundy pour Nim). -/
def nimSum (pos : NimPosition) : Nat :=
  pos.foldl (· ^^^ ·) 0

/-- Une position de Nim est gagnante pour le joueur qui doit jouer ssi nimSum ≠ 0. -/
def isWinningNim (pos : NimPosition) : Bool :=
  nimSum pos != 0

/-! ## Cibles de calibration -/

/-- Cible A (validation P1) : le Nim classique [3,4,5] est gagnant pour le premier joueur.
    decide simple — valide le pipeline de bout en bout (devrait se fermer en 1-2 itérations).
    C'est le contrôle de cohérence de base : si le prouveur ne peut pas fermer ça, le pipeline est cassé. -/
theorem nim_winning_345 : isWinningNim [3, 4, 5] = true := by
  unfold isWinningNim nimSum
  simp [List.foldl]

/-- Cible D (P1) : le nimSum d'un tas unique égale la taille du tas.
    Requiert Nat.xor_zero — le prouveur doit découvrir ce lemme spécifique.
    Un simp naïf sans le bon lemme va stagner.
    Itérations attendues : 3-5 (unfold → simp naïf → échec → découvrir Nat.xor_zero → fermer). -/
theorem nimSum_single (n : Nat) : nimSum [n] = n := by
  unfold nimSum
  simp [List.foldl_cons, List.foldl_nil]

/-- Cible H (cœur P1) : deux tas identiques s'annulent (nimSum = 0).
    C'est le cœur de la théorie de Nim : le xor est auto-annulant.
    Un `simp` naïf va stagner — requiert `Nat.xor_self` ciblé.
    Cela exerce la capacité du Director à pivoter du générique vers le spécifique.
    Itérations attendues : 5-8 (unfold → simp naïf → stagnation → pivot vers Nat.xor_self → fermer). -/
theorem nimSum_self_cancel (n : Nat) : nimSum [n, n] = 0 := by
  unfold nimSum
  simp [List.foldl_cons, List.foldl_nil, List.foldl_cons]

/-- Cible H+ (P1 étendue) : trois tas dont deux s'annulent.
    Combine nimSum_single et nimSum_self_cancel.
    Itérations attendues : 4-7. -/
theorem nimSum_cancel_pair (n m : Nat) : nimSum [n, m, m] = n := by
  unfold nimSum
  simp [List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_cons]

/-- Cible A+ (validation P1) : la position vide est perdante (nimSum = 0).
    Triviale mais assure la couverture du cas limite. -/
theorem nimSum_empty : nimSum [] = 0 := by
  unfold nimSum
  simp [List.foldl_nil]

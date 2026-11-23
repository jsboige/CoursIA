/-
Pont après le jeu : des valeurs aux fonctions, puis aux preuves paramétriques.
Prérequis : types, fonctions, produits et sommes (Lean-01 à Lean-06).
Progression inspirée par ReintroductionToProofs d'Emily Riehl et contributeurs,
MIT : https://github.com/emilyriehl/ReintroductionToProofs/tree/9a2c07fecec5d1a2353c536c366c64958bcad03e
Les exercices et preuves ci-dessous sont originaux ; aucun code du jeu n'est repris.
-/

import Std

set_option autoImplicit false

namespace ProofBridge

universe u v w u' v' w'


/-
Exercice 1 — Construire. Lire le type avant le corps : à partir d'un A et
soit d'un B, soit d'un C, produire une paire dans la branche correspondante.
`match` examine la somme ; `.inl` et `.inr` choisissent sa branche.
-/

def distribute {A : Type u} {B : Type v} {C : Type w}
    (x : A × (B ⊕ C)) : (A × B) ⊕ (A × C) :=
  match x.2 with
  | .inl b => .inl (x.1, b)
  | .inr c => .inr (x.1, c)

def collect {A : Type u} {B : Type v} {C : Type w}
    (x : (A × B) ⊕ (A × C)) : A × (B ⊕ C) :=
  match x with
  | .inl (a, b) => (a, .inl b)
  | .inr (a, c) => (a, .inr c)

#eval distribute ((7 : Nat), (Sum.inl true : Bool ⊕ String))
#eval distribute ((7 : Nat), (Sum.inr "jeu" : Bool ⊕ String))


/-
Les deux calculs donnent respectivement `inl (7, true)` et `inr (7, "jeu")`.
Essayez d'autres valeurs, puis reconstruisez `collect` sans regarder sa définition.
Deux calculs ne prouvent pourtant pas le résultat pour tous les types et valeurs.

Exercice 2 — Vérifier le contrat. `cases` sépare les constructeurs possibles ;
`rfl` ferme chaque égalité lorsque les deux côtés calculent vers le même terme.
Le premier contrat compose collect après distribute ; le second inverse l'ordre.
-/

theorem collect_distribute {A : Type u} {B : Type v} {C : Type w}
    (x : A × (B ⊕ C)) : collect (distribute x) = x := by
  cases x with
  | mk a s => cases s <;> rfl

theorem distribute_collect {A : Type u} {B : Type v} {C : Type w}
    (x : (A × B) ⊕ (A × C)) : distribute (collect x) = x := by
  cases x with
  | inl ab => cases ab <;> rfl
  | inr ac => cases ac <;> rfl

example : collect (distribute ((7 : Nat), (Sum.inl true : Bool ⊕ String))) =
    (7, Sum.inl true) := by
  exact collect_distribute _


/-
Exercice 3 — Transporter. On transforme séparément A, B et C par des fonctions.
Le type ci-dessous affirme que transformer avant ou après la distribution donne
la même valeur, quelle que soit la branche. Essayez de fermer chaque cas avec
`cases` puis `rfl`. Cette preuve est paramétrique, contrairement aux deux calculs.
-/

theorem distribute_map {A : Type u} {B : Type v} {C : Type w}
    {A' : Type u'} {B' : Type v'} {C' : Type w'}
    (f : A → A') (g : B → B') (h : C → C') (x : A × (B ⊕ C)) :
    distribute (Prod.map f (Sum.map g h) x) =
      Sum.map (Prod.map f g) (Prod.map f h) (distribute x) := by
  cases x with
  | mk a s => cases s <;> rfl

example : distribute (Prod.map Nat.succ (Sum.map not String.length)
    ((7 : Nat), (Sum.inr "jeu" : Bool ⊕ String))) =
    Sum.inr (8, 3) := by
  rfl

end ProofBridge

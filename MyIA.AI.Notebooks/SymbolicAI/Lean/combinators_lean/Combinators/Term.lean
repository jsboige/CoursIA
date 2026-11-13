/-
Termes et reduction a un pas des combinateurs S, K, I.

Pli 4 de l'Epic Origami #19742 (grain B, #25061) : confluence du
systeme S/K/I, demontree dans `Combinators.Confluence` en invoquant
l'organe Mathlib `Relation.church_rosser` (Mathlib/Logic/Relation.lean,
l.896 au pin v4.33.0 de ce lake). Ce module pose la syntaxe des termes,
la taille (support de l'induction forte du lemme du losange) et la
relation de reduction a un pas `step`, fermeture contextuelle des trois
regles S, K, I.

L'absence de lieurs rend la reduction des combinateurs nettement plus
simple que celle du lambda-calcul : la reduction parallele
(`Combinators.Parallel`) est une fermeture directe, sans substitution
de variables capturees.

References : Hindley & Seldin, *Lambda-Calculus and Combinators, an
Introduction* (2008), ch. 2 ; Wolfram, *Combinators: A Centennial
View* (2020), ch. 3 et 11.
-/

import Mathlib.Tactic

namespace Combinators

/-- Termes des combinateurs S, K, I : trois atomes et l'application
binaire. Pas de lieurs. -/
inductive Term where
  | S : Term
  | K : Term
  | I : Term
  | app : Term → Term → Term

/-- Notation infixe pour l'application, associative a gauche. -/
scoped infixl:70 " ⊙ " => Term.app

open Term

/-- Taille d'un terme : 1 pour un atome, 1 + fils pour une application.
Sert de mesure a l'induction forte du lemme du losange. -/
def Term.size : Term → Nat
  | S | K | I => 1
  | app x y => 1 + Term.size x + Term.size y

@[simp] theorem Term.size_S : Term.size S = 1 := rfl

@[simp] theorem Term.size_K : Term.size K = 1 := rfl

@[simp] theorem Term.size_I : Term.size I = 1 := rfl

@[simp] theorem Term.size_app (x y : Term) :
    Term.size (x ⊙ y) = 1 + Term.size x + Term.size y := rfl

theorem Term.size_pos (t : Term) : 0 < Term.size t := by
  cases t <;> simp only [Term.size] <;> omega

/-- Reduction a un pas : fermeture contextuelle des trois regles.
Un redex peut se contracter n'importe ou dans le terme.

  - S : `S ⊙ x ⊙ y ⊙ z ↝ x ⊙ z ⊙ (y ⊙ z)`
  - K : `K ⊙ x ⊙ y ↝ x`
  - I : `I ⊙ x ↝ x`
-/
inductive step : Term → Term → Prop
  | S (x y z : Term) : step (S ⊙ x ⊙ y ⊙ z) (x ⊙ z ⊙ (y ⊙ z))
  | K (x y : Term) : step (K ⊙ x ⊙ y) x
  | I (x : Term) : step (I ⊙ x) x
  | app_l {x x' y : Term} (h : step x x') : step (x ⊙ y) (x' ⊙ y)
  | app_r {x y y' : Term} (h : step y y') : step (x ⊙ y) (x ⊙ y')

end Combinators

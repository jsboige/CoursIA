/-
Bridge after the game: from values to functions, then parametric proofs.
Prerequisites: types, functions, products and sums (Lean-01 through Lean-06).
Progression inspired by ReintroductionToProofs by Emily Riehl and contributors,
MIT: https://github.com/emilyriehl/ReintroductionToProofs/tree/9a2c07fecec5d1a2353c536c366c64958bcad03e
The exercises and proofs below are original; no game code is copied.
-/

import Std

set_option autoImplicit false

namespace ProofBridge_en

universe u v w u' v' w'


/-
Exercise 1 — Construct. Read the type before the body: from an A and
either a B or a C, produce a pair in the corresponding branch.
`match` inspects the sum; `.inl` and `.inr` choose its branch.
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
The two computations yield `inl (7, true)` and `inr (7, "jeu")` respectively.
Try other values, then rebuild `collect` without looking at its definition.
Two computations do not prove the result for every type and value, however.

Exercise 2 — Check the contract. `cases` separates the possible constructors;
`rfl` closes each equality when both sides compute to the same term.
The first contract composes collect after distribute; the second reverses the order.
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
Exercise 3 — Transport. Transform A, B and C separately with functions.
The type below states that transforming before or after distribution gives
the same value, regardless of the branch. Try closing each case with
`cases` then `rfl`. This proof is parametric, unlike the two computations.
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

end ProofBridge_en

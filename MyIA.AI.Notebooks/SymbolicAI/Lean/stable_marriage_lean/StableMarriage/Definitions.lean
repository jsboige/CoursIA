/-
  Stable Marriage - Definitions
  ==============================

  Core types and definitions for the stable marriage problem.
  We model n men and n women (both as Fin n), each with strict preference
  rankings over the opposite set.

  A matching is a bijection between men and women.
  A matching is stable iff no blocking pair exists.
-/

namespace StableMarriage

open Finset Function

variable {n : Nat} [NeZero n]

/-- A man is identified by Fin n -/
abbrev Man (n : Nat) := Fin n

/-- A woman is identified by Fin n -/
abbrev Woman (n : Nat) := Fin n

/--
A preference ordering for a person over the opposite set.
Represented as a function mapping each candidate to a rank (lower = preferred).
Strict preference means the ranking function is injective.
-/
structure PrefProfile (n : Nat) [NeZero n] where
  /-- Men's preferences: each man ranks all women -/
  menPref : Fin n → Fin n → Fin n
  /-- Women's preferences: each woman ranks all men -/
  womenPref : Fin n → Fin n → Fin n
  /-- Each man's ranking is a permutation (bijective) -/
  menPref_bijective : ∀ m, Bijective (menPref m)
  /-- Each woman's ranking is a permutation (bijective) -/
  womenPref_bijective : ∀ w, Bijective (womenPref w)

namespace PrefProfile

variable {n : Nat} [NeZero n] (prof : PrefProfile n)

/--
Man `m` prefers woman `w1` over woman `w2` iff w1 has a lower rank.
Since menPref m is a bijection Fin n → Fin n, lower = more preferred.
-/
def manPrefers (m : Fin n) (w1 w2 : Fin n) : Bool :=
  prof.menPref m w1 < prof.menPref m w2

/--
Woman `w` prefers man `m1` over man `m2` iff m1 has a lower rank.
-/
def womanPrefers (w : Fin n) (m1 m2 : Fin n) : Bool :=
  prof.womenPref w m1 < prof.womenPref w m2

/--
Man `m` strictly prefers woman `w1` to woman `w2`.
Prop-valued version for theorem statements.
-/
def ManPrefers (m : Fin n) (w1 w2 : Fin n) : Prop :=
  prof.menPref m w1 < prof.menPref m w2

/--
Woman `w` strictly prefers man `m1` to man `m2`.
-/
def WomanPrefers (w : Fin n) (m1 m2 : Fin n) : Prop :=
  prof.womenPref w m1 < prof.womenPref w m2

end PrefProfile

/--
A matching is a bijection from men to women (perfect matching).
-/
structure Matching (n : Nat) [NeZero n] where
  /-- Map each man to his matched woman -/
  spouse : Fin n → Fin n
  /-- The matching is bijective (each woman matched to exactly one man) -/
  bijective : Bijective spouse

namespace Matching

variable {n : Nat} [NeZero n] (μ : Matching n)

/-- Get the inverse: which man is matched to woman w -/
def inverse (w : Fin n) : Fin n :=
  (Equiv.ofBijective μ.spouse μ.bijective).symm w

end Matching

/--
A blocking pair for matching μ under preference profile prof:
a man m and woman w who both prefer each other to their current partners.
-/
def IsBlockingPair (prof : PrefProfile n) (μ : Matching n)
    (m : Fin n) (w : Fin n) : Prop :=
  prof.ManPrefers m w (μ.spouse m) ∧
  prof.WomanPrefers w m (μ.inverse w)

/--
A matching is stable iff no blocking pair exists.
-/
def IsStable (prof : PrefProfile n) (μ : Matching n) : Prop :=
  ∀ m w, ¬ IsBlockingPair prof μ m w

/--
A matching is man-optimal iff every man gets their best possible partner
among all stable matchings.
-/
def IsManOptimal (prof : PrefProfile n) (μ : Matching n) : Prop :=
  IsStable prof μ ∧
  ∀ μ' : Matching n, IsStable prof μ' →
    ∀ m : Fin n, prof.menPref m (μ.spouse m) ≤ prof.menPref m (μ'.spouse m)

end StableMarriage

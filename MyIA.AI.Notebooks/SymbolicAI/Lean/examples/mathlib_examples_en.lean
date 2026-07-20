/-
  Lean Examples - Mathlib Usage (EN sibling)

  This file contains Mathlib4 usage examples
  corresponding to the Lean-6 notebook.

  NOTE: These examples require Mathlib to be installed.
  Without Mathlib, this file will not compile.

  English sibling of mathlib_examples.lean (i18n #4980): docstrings and
  comments translated to English; theorems, definitions, tactics, and
  variables are byte-identical to the French original.
-/

-- Uncomment the imports if Mathlib is installed:
-- import Mathlib.Tactic
-- import Mathlib.Data.Nat.Prime
-- import Mathlib.Algebra.Ring.Basic

-- ============================================================
-- Examples without Mathlib (work with base Lean)
-- ============================================================

-- omega : linear arithmetic
theorem omega_example_1 (n m : Nat) (h : n < m) : n + 1 <= m := by
  omega

theorem omega_example_2 (a b c : Int) (h1 : a + b = c) (h2 : a - b = 0) : 2 * a = c := by
  omega

-- decide : decidable propositions
theorem decide_example_1 : 7 * 8 = 56 := by rfl
theorem decide_example_2 : 100 > 50 := by decide

-- ============================================================
-- Examples with Mathlib (uncomment if Mathlib is available)
-- ============================================================

/-
-- ring : polynomial algebra
example (a b : Int) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring
example (a b : Int) : a^2 - b^2 = (a + b) * (a - b) := by ring
example (x y z : Int) : (x + y + z)^2 = x^2 + y^2 + z^2 + 2*x*y + 2*x*z + 2*y*z := by ring

-- linarith : linear inequalities
example (x : Int) (h : x > 5) : x >= 5 := by linarith
example (x y : Int) (h1 : x <= y) (h2 : y <= x + 3) : y - x <= 3 := by linarith

-- norm_num : numerical computations
example : (2 : Nat) + 2 = 4 := by norm_num
example : (123 : Nat) * 456 = 56088 := by norm_num
example : Nat.Prime 17 := by norm_num

-- field_simp : simplification in fields
example (a b : Rat) (hb : b ≠ 0) : a / b * b = a := by field_simp
-/

-- ============================================================
-- Algebraic structures (Mathlib concepts without import)
-- ============================================================

-- Simplified definition of a monoid
class MyMonoid (M : Type) where
  one : M
  mul : M -> M -> M
  one_mul : forall a : M, mul one a = a
  mul_one : forall a : M, mul a one = a
  mul_assoc : forall a b c : M, mul (mul a b) c = mul a (mul b c)

-- Nat is an additive monoid
instance : MyMonoid Nat where
  one := 0
  mul := Nat.add
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero
  mul_assoc := Nat.add_assoc

-- ============================================================
-- Number theory (basic concepts)
-- ============================================================

-- Definition of a prime number (simplified)
def myPrime (n : Nat) : Prop :=
  n > 1 /\ forall d : Nat, d > 0 -> d < n -> n % d = 0 -> d = 1

-- 2 is prime
theorem two_is_prime : myPrime 2 := by
  constructor
  . decide
  . intro d hd1 hd2 hdiv
    omega

-- ============================================================
-- Theorem search
-- ============================================================

-- Useful commands for exploring Mathlib:
-- #check Nat.add_comm
-- #check Nat.mul_comm
-- #print Nat.add_assoc

-- Search with exact? and apply?:
-- example (n : Nat) : n + 0 = n := by exact?
-- example (n m : Nat) : n <= n + m := by apply?

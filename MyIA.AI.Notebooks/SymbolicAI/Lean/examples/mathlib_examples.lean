/-
  Lean Examples - Mathlib Usage

  Ce fichier contient des exemples d'utilisation de Mathlib4
  correspondant au notebook Lean-6.

  NOTE: Ces exemples necessitent Mathlib installe.
  Sans Mathlib, ce fichier ne compilera pas.
-/

-- Decommenter les imports si Mathlib est installe:
-- import Mathlib.Tactic
-- import Mathlib.Data.Nat.Prime
-- import Mathlib.Algebra.Ring.Basic

-- ============================================================
-- Exemples sans Mathlib (fonctionnent avec Lean de base)
-- ============================================================

-- omega : arithmetique lineaire
theorem omega_example_1 (n m : Nat) (h : n < m) : n + 1 <= m := by
  omega

theorem omega_example_2 (a b c : Int) (h1 : a + b = c) (h2 : a - b = 0) : 2 * a = c := by
  omega

-- decide : propositions decidables
theorem decide_example_1 : 7 * 8 = 56 := by rfl
theorem decide_example_2 : 100 > 50 := by decide

-- ============================================================
-- Exemples avec Mathlib (decommenter si Mathlib disponible)
-- ============================================================

/-
-- ring : algebre polynomiale
example (a b : Int) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring
example (a b : Int) : a^2 - b^2 = (a + b) * (a - b) := by ring
example (x y z : Int) : (x + y + z)^2 = x^2 + y^2 + z^2 + 2*x*y + 2*x*z + 2*y*z := by ring

-- linarith : inegalites lineaires
example (x : Int) (h : x > 5) : x >= 5 := by linarith
example (x y : Int) (h1 : x <= y) (h2 : y <= x + 3) : y - x <= 3 := by linarith

-- norm_num : calculs numeriques
example : (2 : Nat) + 2 = 4 := by norm_num
example : (123 : Nat) * 456 = 56088 := by norm_num
example : Nat.Prime 17 := by norm_num

-- field_simp : simplification dans les corps
example (a b : Rat) (hb : b ≠ 0) : a / b * b = a := by field_simp
-/

-- ============================================================
-- Structures algebriques (Mathlib concepts sans import)
-- ============================================================

-- Definition simplifiee d'un monoide
class MyMonoid (M : Type) where
  one : M
  mul : M -> M -> M
  one_mul : forall a : M, mul one a = a
  mul_one : forall a : M, mul a one = a
  mul_assoc : forall a b c : M, mul (mul a b) c = mul a (mul b c)

-- Nat est un monoide additif
instance : MyMonoid Nat where
  one := 0
  mul := Nat.add
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero
  mul_assoc := Nat.add_assoc

-- ============================================================
-- Theorie des nombres (concepts de base)
-- ============================================================

-- Definition de nombre premier (simplifiee)
def myPrime (n : Nat) : Prop :=
  n > 1 /\ forall d : Nat, d > 0 -> d < n -> n % d = 0 -> d = 1

-- 2 est premier
theorem two_is_prime : myPrime 2 := by
  constructor
  . decide
  . intro d hd1 hd2 hdiv
    omega

-- ============================================================
-- Recherche de theoremes
-- ============================================================

-- Commandes utiles pour explorer Mathlib:
-- #check Nat.add_comm
-- #check Nat.mul_comm
-- #print Nat.add_assoc

-- Recherche avec exact? et apply?:
-- example (n : Nat) : n + 0 = n := by exact?
-- example (n m : Nat) : n <= n + m := by apply?

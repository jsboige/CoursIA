import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
-- omega est fourni par Lean core (plus de module Mathlib.Tactic.Omega depuis v4.30)

/-!
# Basic Mathlib Examples

Ce fichier contient des exemples simples utilisant les tactiques Mathlib
pour tester que l'installation fonctionne correctement.
-/

-- Exemple avec ring
example (a b : ℤ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

-- Exemple avec linarith
example (x y : ℚ) (h1 : x ≤ 3*y) (h2 : y ≤ 1) : x ≤ 3 := by linarith

-- Exemple avec omega
example (n : ℕ) : n < n + 1 := by omega

-- Exemple combiné
example (a b c : ℤ) (h1 : a = b) (h2 : b = c) : a + a = 2 * c := by
  rw [h1, h2]
  ring

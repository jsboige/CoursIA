/-
Corps de definitions du probleme d'affectation (issue #12598).

Un probleme d'affectation a n agents et n taches, une matrice de couts
`C i j` (entiers : l'algorithme pedagogique du notebook travaille en
arithmetique entiere exacte, cf GT-27 section 2). Une affectation est un
matching parfait, c'est-a-dire une permutation de `Fin n` ; sa valeur est
la somme des couts des aretes empruntees.
-/
import Mathlib

namespace Assignment

variable {n : ℕ} (C : Fin n → Fin n → ℤ)

/-- Valeur d'une affectation : somme des couts des aretes du matching. -/
def value (σ : Equiv.Perm (Fin n)) : ℤ := ∑ i, C i (σ i)

/-- `σ` est optimale si aucune affectation ne fait strictement mieux
(valeur minimale — le notebook minimise les couts). -/
def IsOptimal (σ : Equiv.Perm (Fin n)) : Prop := ∀ τ, value C σ ≤ value C τ

end Assignment

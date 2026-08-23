/-
Core definitions of the assignment problem (issue #12598).

An assignment problem has n agents and n tasks, a cost matrix `C i j`
(integers: the notebook's pedagogical algorithm works in exact integer
arithmetic, cf GT-27 section 2). An assignment is a perfect matching,
i.e. a permutation of `Fin n`; its value is the sum of the costs of the
edges it uses.
-/
import Mathlib

namespace Assignment_en

variable {n : ℕ} (C : Fin n → Fin n → ℤ)

/-- Value of an assignment: sum of the matching edge costs. -/
def value (σ : Equiv.Perm (Fin n)) : ℤ := ∑ i, C i (σ i)

/-- `σ` is optimal if no assignment does strictly better (minimal value
— the notebook minimizes costs). -/
def IsOptimal (σ : Equiv.Perm (Fin n)) : Prop := ∀ τ, value C σ ≤ value C τ

end Assignment_en

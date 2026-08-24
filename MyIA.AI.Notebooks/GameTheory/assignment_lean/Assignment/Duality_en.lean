/-
Dual potentials of the assignment problem (issue #12598).

The LP primal minimizes `∑ i j, C i j * x i j` under row and column
constraints; its dual maximizes `∑ i, u i + ∑ j, v j` under the constraint
`u i + v j ≤ C i j` for every pair. These potentials are exactly the labels
of the Kuhn-Munkres algorithm: dual feasibility is the invariant maintained
throughout, and the Hungarian tightening (cf KuhnMunkres.lean) never breaks
it.

The central result of this file is weak duality: every (feasible)
assignment has value at least that of any feasible dual pair. This is the
bound that, met with equality, certifies optimality (cf Optimality.lean).
-/
import Mathlib
import Assignment.Definitions_en

namespace Assignment_en

variable {n : ℕ} (C : Fin n → Fin n → ℤ) (u v : Fin n → ℤ)

/-- Dual feasibility: `u i + v j ≤ C i j` for every pair (i, j). -/
def DualFeasible : Prop := ∀ i j, u i + v j ≤ C i j

/-- Dual value: sum of all the potentials. -/
def dualValue : ℤ := (∑ i, u i) + (∑ j, v j)

/-- **Weak duality**: every assignment sits above the dual value.

The computation reindexes `∑ j, v j` along the permutation `σ`
(a perfect matching visits every column exactly once), then bounds term by
term using dual feasibility. This is the first half of the
Kuhn-Munkres optimality certificate. -/
theorem weak_duality (h : DualFeasible C u v) (σ : Equiv.Perm (Fin n)) :
    dualValue u v ≤ value C σ := by
  have hreindex : (∑ i, v (σ i : Fin n)) = ∑ j, v j :=
    Equiv.sum_comp σ (fun j => v j)
  calc dualValue u v
      = ∑ i, (u i + v (σ i : Fin n)) := by
        rw [Finset.sum_add_distrib, hreindex]
        rfl
    _ ≤ ∑ i, C i (σ i) := Finset.sum_le_sum fun i _ => h i (σ i)
    _ = value C σ := rfl

end Assignment_en

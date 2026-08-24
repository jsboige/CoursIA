/-
Optimality certificate by duality (issue #12598).

The bridge between the dual machinery (Duality.lean) and the algorithmic
question (the optimality notion of Definitions.lean): a feasible dual pair
whose value equals that of an assignment `σ` proves `σ` optimal — zero
duality gap; the theorem the GT-27 notebook verifies numerically (triple
test, section 3) becomes a proof checked by the Lean kernel.

The second route to the zero gap: if every matching edge is an equality
edge (`u i + v (σ i) = C i (σ i)`), the primal and dual values coincide
automatically — this is the output invariant of the Kuhn-Munkres algorithm
(cf KuhnMunkres.lean).
-/
import Mathlib
import Assignment.Duality_en

namespace Assignment_en

variable {n : ℕ} (C : Fin n → Fin n → ℤ) (u v : Fin n → ℤ) (σ : Equiv.Perm (Fin n))

/-- If every matching edge is an equality edge, the dual value equals the
primal value (reindexing `∑ v` along `σ`). -/
theorem dualValue_eq_of_edges (h : ∀ i, u i + v (σ i : Fin n) = C i (σ i)) :
    dualValue u v = value C σ := by
  have hreindex : (∑ i, v (σ i : Fin n)) = ∑ j, v j :=
    Equiv.sum_comp σ (fun j => v j)
  calc dualValue u v
      = ∑ i, (u i + v (σ i : Fin n)) := by
        rw [Finset.sum_add_distrib, hreindex]
        rfl
    _ = ∑ i, C i (σ i) := Finset.sum_congr rfl fun i _ => h i
    _ = value C σ := rfl

/-- **Optimality certificate with zero gap**: feasible dual + dual value
equal to the value of `σ` ⇒ `σ` is optimal. This is exactly the shape of
the certificate the Hungarian method produces on termination. -/
theorem optimality_of_zero_gap (h : DualFeasible C u v)
    (heq : dualValue u v = value C σ) : IsOptimal C σ := by
  intro τ
  rw [← heq]
  exact weak_duality C u v h τ

end Assignment_en

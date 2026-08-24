/-
Correction skeleton of the Kuhn-Munkres algorithm (issue #12598).

Kuhn (1955) after Konig and Egervary; Munkres (1957) for the strongly
polynomial time proof. The complete pedagogical implementation lives in
the GT-27 notebook (Hungarian tree BFS, dual tightening); this file
formalizes the correction structure:

1. the **equality graph** — the pairs where the dual constraint is tight;
2. the **output invariant** — an assignment whose every edge lies in the
   equality graph, together with a feasible dual, is optimal (assembling
   Duality + Optimality);
3. the **Hungarian tightening** — the operation that shifts the potentials
   (`u += δ` on a set of rows, `v -= δ` on a set of columns) preserves
   dual feasibility, under the hypothesis that `δ` exceeds the margin of
   no outgoing edge (tightened rows x untightened columns). This is
   exactly the algorithm's `delta = min margin`.

Out of scope (deliberately, cf issue): the termination proof and the
O(n³) complexity — structural correction by duality suffices.
-/
import Mathlib
import Assignment.Optimality_en

namespace Assignment_en

variable {n : ℕ} (C : Fin n → Fin n → ℤ) (u v : Fin n → ℤ)

/-- Equality edge: the pair `(i, j)` saturates the dual constraint
(`u i + v j = C i j`). The equality graph is the union of these edges;
the algorithm's Hungarian tree lives exclusively in it. -/
def EqEdge (i j : Fin n) : Prop := u i + v j = C i j

/-- **Kuhn-Munkres output invariant**: if the final potential is
dual-feasible and every edge of `σ` is an equality edge, then `σ` is
optimal. This is the certificate produced on termination: the Hungarian
method never asks any step to trust an external solver. -/
theorem kuhn_munkres_correct (σ : Equiv.Perm (Fin n)) (h : DualFeasible C u v)
    (heq : ∀ i, EqEdge C u v i (σ i)) : IsOptimal C σ :=
  optimality_of_zero_gap C u v σ h (dualValue_eq_of_edges C u v σ heq)

/-- **The Hungarian tightening preserves dual feasibility.**

Given a set of rows `S` and columns `T` (the Hungarian tree and its
discovered columns), a `δ ≥ 0` bounded above by the margin of every
outgoing edge (`i ∈ S`, `j ∉ T`) yields a new still-feasible dual pair:
internal edges `(S, T)` see their two contributions move in opposite
directions, incoming edges `(∉ S, T)` only go down, and outgoing edges
`(S, ∉ T)` stay below their cost by the hypothesis on `δ`. The algorithm's
`δ = min margin` satisfies the hypothesis by definition of the minimum. -/
theorem dualFeasible_tighten (S T : Finset (Fin n)) (h : DualFeasible C u v)
    (δ : ℤ) (hδ : 0 ≤ δ)
    (hmargin : ∀ i ∈ S, ∀ j ∉ T, δ ≤ C i j - (u i + v j)) :
    DualFeasible C (fun i => if i ∈ S then u i + δ else u i)
                 (fun j => if j ∈ T then v j - δ else v j) := by
  intro i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ T
    · -- internal edge: the two contributions cancel out
      simp only [if_pos hi, if_pos hj]
      have h₀ : u i + v j ≤ C i j := h i j
      linarith
    · -- outgoing edge: bounded by the margin hypothesis on delta
      simp only [if_pos hi, if_neg hj]
      have h₀ : u i + v j ≤ C i j := h i j
      have h₁ : δ ≤ C i j - (u i + v j) := hmargin i hi j hj
      linarith
  · by_cases hj : j ∈ T
    · -- incoming edge: the contribution of v only goes down
      simp only [if_neg hi, if_pos hj]
      have h₀ : u i + v j ≤ C i j := h i j
      linarith
    · -- untouched edge
      simp only [if_neg hi, if_neg hj]
      exact h i j

end Assignment_en

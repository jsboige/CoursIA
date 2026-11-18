/-
Counting perfect matchings: the permanent as a bridge (issue #21958, fold 6 of #19898).

Duality (Duality_en.lean) exhibits an optimal matching in polynomial time;
counting ALL perfect matchings belongs to another class (#P-hard,
openai/math family 113) and the matching polytope admits no compact
semidefinite lift (family 126). This file formalizes the bridge between
the two worlds: the Mathlib permanent
(Mathlib.LinearAlgebra.Matrix.Permanent) of the 0/1 adjacency matrix
equals the cardinality of the perfect matchings of the bipartite graph.

Organ-first (#13564): `Matrix.permanent` is the native organ; this file
redefines nothing, it proves the permanent <-> matchings correspondence.
-/
import Mathlib

namespace Assignment_en

open Matrix

variable {n : ℕ}

/-- Integer adjacency matrix of a bipartite graph on `Fin n × Fin n`:
`1` if the edge exists, `0` otherwise. -/
def adjMatrix (B : Matrix (Fin n) (Fin n) Bool) : Matrix (Fin n) (Fin n) ℕ :=
  B.map fun b => if b then 1 else 0

/-- The set of perfect matchings of a bipartite graph: the permutations
whose every edge from row `i` to column `σ i` is present. -/
def perfectMatchingSet (B : Matrix (Fin n) (Fin n) Bool) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ => ∀ i, B i (σ i)

/-- A product of 0/1 indicators equals 1 exactly when every edge is
present, 0 otherwise. Technical lemma of the bridge. -/
theorem prod_ite_eq_one_iff (B : Matrix (Fin n) (Fin n) Bool)
    (σ : Equiv.Perm (Fin n)) :
    (∏ i, (if B i (σ i) then (1:ℕ) else 0)) = if ∀ i, B i (σ i) then 1 else 0 := by
  by_cases h : ∀ i, B i (σ i)
  · simp [h]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    have hz : (if B i (σ i) then (1:ℕ) else 0) = 0 := by
      cases hBi : B i (σ i) with
      | false => simp
      | true => exact absurd hBi hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz

/-- **The bridge**: the (Mathlib) permanent of the 0/1 adjacency matrix
equals the number of perfect matchings of the bipartite graph. This is the
local formalization of the entry point of openai/math families 113 (FPRAS
for counting) and 126 (SDP closure), quoted with their epistemic status in
notebook ANALYSE-12. -/
theorem card_eq_permanent (B : Matrix (Fin n) (Fin n) Bool) :
    (perfectMatchingSet B).card = (adjMatrix B).permanent := by
  classical
  calc (perfectMatchingSet B).card
      = ∑ σ : Equiv.Perm (Fin n), (if ∀ i, B i (σ i) then (1:ℕ) else 0) := by
        simp only [perfectMatchingSet]
        exact Finset.card_filter _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, (if B i (σ i) then (1:ℕ) else 0) :=
        Finset.sum_congr rfl fun σ _ => (prod_ite_eq_one_iff B σ).symm
    _ = ((adjMatrix B)ᵀ).permanent := rfl
    _ = (adjMatrix B).permanent := Matrix.permanent_transpose _

/-- Complete bipartite graph: every permutation is covering, the
cardinality is the factorial. -/
theorem card_eq_factorial (B : Matrix (Fin n) (Fin n) Bool) (h : ∀ i j, B i j) :
    (perfectMatchingSet B).card
      = (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
  simp [perfectMatchingSet, h]

/-- Corollary of the bridge on the complete graph: the permanent of the
all-one matrix is the factorial of n (cross-checked with `Fintype.card_perm`). -/
theorem permanent_complete_eq_factorial (B : Matrix (Fin n) (Fin n) Bool)
    (h : ∀ i j, B i j) :
    (adjMatrix B).permanent = Nat.factorial (Fintype.card (Fin n)) := by
  rw [← card_eq_permanent B, card_eq_factorial B h, Finset.card_univ,
    Fintype.card_perm]

end Assignment_en

/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Kochen-Specker Theorem (18-vector Cabello proof)

No `{0, 1}`-coloring of the 18 unit vectors of R^4 listed below is compatible
with the orthogonality constraint: in every orthogonal basis (4 mutually
orthogonal vectors), exactly one vector receives color `1`.

This is the combinatorial kernel used in the Conway-Kochen Free Will Theorem
(Pilier 1 of Epic #1651). The 18-vector proof is due to Cabello, Estebaranz
and Garcia-Alcaine (1996), tightening the original 117-vector proof by
Kochen and Specker (1967), the 33-vector proof of Peres (1991), and the
20-vector construction of Kernaghan (1994).

Source: Cabello, Estebaranz, Garcia-Alcaine,
       "Bell-Kochen-Specker theorem: A proof with 18 vectors",
       Phys. Lett. A 212 (1996), 183-187.
Table: Wikipedia "Kochen-Specker theorem" (Overview section), which
       reproduces the original Cabello et al. table.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic


/-
  English mirror of `KochenSpecker.lean` (FR canonical). Convention EPIC #4980
  (decision ratified 2026-07-04, cf `code-style.md` paragraphe Lean i18n): distinct FR + EN sibling
  files - no inline bilingual block in a single file (Option B rejected). The module
  docstring above mirrors the FR copyright + FR-orbit description; the body signatures,
  proofs and tactics remain byte-identical between the two files.
-/

namespace Conway_en

open Conway_en

namespace KochenSpecker_en

/-!
## The 18 Cabello vectors and 9 orthogonal bases (R^4)

The 9 orthogonal bases (contexts) are columns of the following table.
Each column contains 4 mutually orthogonal vectors of R^4. Every vector
appears in exactly 2 columns, yielding the overlap structure that
enables the parity contradiction.

Columns (bases) of the Cabello table:

  C0:  (0,0,0,1)  (0,0,1,0)  (1,1,0,0)  (1,-1,0,0)
  C1:  (0,0,0,1)  (0,1,0,0)  (1,0,1,0)  (1,0,-1,0)
  C2:  (1,-1,1,-1) (1,-1,-1,1) (1,1,0,0) (0,0,1,1)
  C3:  (1,-1,1,-1) (1,1,1,1)   (1,0,-1,0) (0,1,0,-1)
  C4:  (0,0,1,0)  (0,1,0,0)  (1,0,0,1)  (1,0,0,-1)
  C5:  (1,-1,-1,1) (1,1,1,1)  (1,0,0,-1) (0,1,-1,0)
  C6:  (1,1,-1,1) (1,1,1,-1)  (1,-1,0,0) (0,0,1,1)
  C7:  (1,1,-1,1) (-1,1,1,1)  (1,0,1,0)  (0,1,0,-1)
  C8:  (1,1,1,-1) (-1,1,1,1)  (1,0,0,1)  (0,1,-1,0)

The 18 distinct vectors (after deduplication across columns):

  v0  = (0,0,0,1)   v9  = (0,0,1,1)
  v1  = (0,0,1,0)   v10 = (1,1,1,1)
  v2  = (1,1,0,0)   v11 = (0,1,0,-1)
  v3  = (1,-1,0,0)  v12 = (1,0,0,1)
  v4  = (0,1,0,0)   v13 = (1,0,0,-1)
  v5  = (1,0,1,0)   v14 = (0,1,-1,0)
  v6  = (1,0,-1,0)  v15 = (1,1,-1,1)
  v7  = (1,-1,1,-1) v16 = (1,1,1,-1)
  v8  = (1,-1,-1,1) v17 = (-1,1,1,1)

Overlap structure (each vector in exactly 2 contexts):

  v0  ∈ {C0,C1}   v6  ∈ {C1,C3}   v12 ∈ {C4,C8}
  v1  ∈ {C0,C4}   v7  ∈ {C2,C3}   v13 ∈ {C4,C5}
  v2  ∈ {C0,C2}   v8  ∈ {C2,C5}   v14 ∈ {C5,C8}
  v3  ∈ {C0,C6}   v9  ∈ {C2,C6}   v15 ∈ {C6,C7}
  v4  ∈ {C1,C4}   v10 ∈ {C3,C5}   v16 ∈ {C6,C8}
  v5  ∈ {C1,C7}   v11 ∈ {C3,C7}   v17 ∈ {C7,C8}
-/

/-!
## Abstract formulation

Rather than formalizing the exact R^4 coordinates and orthogonality
predicates (which require Real-valued inner products), we state the
theorem combinatorially: given 18 abstract vector indices and 9
contexts of size 4 with the Cabello overlap, no {0,1}-coloring
satisfying "exactly one 1 per context" exists.

The orthogonality of each context is implicit in the index encoding:
`contextMembers` reflects the Cabello table; verifying the inner
products vanish is a separate (computational) lemma left for the
geometric formalization (Pilier 2).
-/

/-- An abstract index for the 18 distinct vectors. -/
abbrev VecIdx := Fin 18

/-- An abstract index for the 9 orthogonal bases (contexts). -/
abbrev ContextIdx := Fin 9

/-- Context membership: which 4 vector indices form each orthogonal basis.
    Encodes the Cabello overlap structure where each vector appears
    in exactly 2 contexts. -/
def contextMembers : ContextIdx → Fin 4 → VecIdx
  -- C0: standard basis-like {v0, v1, v2, v3}
  | 0, 0 => 0   -- (0,0,0,1)
  | 0, 1 => 1   -- (0,0,1,0)
  | 0, 2 => 2   -- (1,1,0,0)
  | 0, 3 => 3   -- (1,-1,0,0)
  -- C1: {v0, v4, v5, v6}
  | 1, 0 => 0   -- (0,0,0,1)   shared with C0
  | 1, 1 => 4   -- (0,1,0,0)
  | 1, 2 => 5   -- (1,0,1,0)
  | 1, 3 => 6   -- (1,0,-1,0)
  -- C2: {v7, v8, v2, v9}
  | 2, 0 => 7   -- (1,-1,1,-1)
  | 2, 1 => 8   -- (1,-1,-1,1)
  | 2, 2 => 2   -- (1,1,0,0)    shared with C0
  | 2, 3 => 9   -- (0,0,1,1)
  -- C3: {v7, v10, v6, v11}
  | 3, 0 => 7   -- (1,-1,1,-1)  shared with C2
  | 3, 1 => 10  -- (1,1,1,1)
  | 3, 2 => 6   -- (1,0,-1,0)   shared with C1
  | 3, 3 => 11  -- (0,1,0,-1)
  -- C4: {v1, v4, v12, v13}
  | 4, 0 => 1   -- (0,0,1,0)    shared with C0
  | 4, 1 => 4   -- (0,1,0,0)    shared with C1
  | 4, 2 => 12  -- (1,0,0,1)
  | 4, 3 => 13  -- (1,0,0,-1)
  -- C5: {v8, v10, v13, v14}
  | 5, 0 => 8   -- (1,-1,-1,1)  shared with C2
  | 5, 1 => 10  -- (1,1,1,1)    shared with C3
  | 5, 2 => 13  -- (1,0,0,-1)   shared with C4
  | 5, 3 => 14  -- (0,1,-1,0)
  -- C6: {v15, v16, v3, v9}
  | 6, 0 => 15  -- (1,1,-1,1)
  | 6, 1 => 16  -- (1,1,1,-1)
  | 6, 2 => 3   -- (1,-1,0,0)   shared with C0
  | 6, 3 => 9   -- (0,0,1,1)    shared with C2
  -- C7: {v15, v17, v5, v11}
  | 7, 0 => 15  -- (1,1,-1,1)   shared with C6
  | 7, 1 => 17  -- (-1,1,1,1)
  | 7, 2 => 5   -- (1,0,1,0)    shared with C1
  | 7, 3 => 11  -- (0,1,0,-1)   shared with C3
  -- C8: {v16, v17, v12, v14}
  | 8, 0 => 16  -- (1,1,1,-1)   shared with C6
  | 8, 1 => 17  -- (-1,1,1,1)   shared with C7
  | 8, 2 => 12  -- (1,0,0,1)    shared with C4
  | 8, 3 => 14  -- (0,1,-1,0)   shared with C5

/-- A {0,1}-coloring of the 18 vectors. -/
def Coloring := VecIdx → Bool

/-- A coloring is valid iff every context (orthogonal basis) has
    exactly one vector colored `true`. -/
def IsValidColoring (c : Coloring) : Prop :=
  ∀ k : ContextIdx,
    (∑ i : Fin 4, if c (contextMembers k i) then (1 : ℕ) else 0) = 1

/-- Key property: each of the 18 vectors appears in exactly 2 contexts.
    This is the Cabello overlap structure that enables the parity proof. -/
lemma each_vector_in_two_contexts (v : VecIdx) :
    (∑ k : ContextIdx, ∑ i : Fin 4,
      if contextMembers k i = v then (1 : ℕ) else 0) = 2 := by
  fin_cases v <;> decide

/-- **Kochen-Specker Theorem (18-vector Cabello proof)**.
    There is no valid {0,1}-coloring of the 18 vectors compatible
    with the orthogonality constraint.

    Proof sketch (parity argument):
    1. A valid coloring assigns exactly one `1` per context, so summing
       over all 9 contexts gives a total of 9 ones (counted with
       multiplicity over contexts).
    2. Reordering the double sum: each vector `v` contributes
       `(number of contexts containing v) * c(v)` to the total.
       By `each_vector_in_two_contexts`, that factor is always 2.
    3. Hence the total ones = 2 * (number of vectors colored `1`),
       which is even.
    4. But 9 is odd. Contradiction. -/
theorem kochen_specker : ¬ ∃ c : Coloring, IsValidColoring c := by
  rintro ⟨c, hc⟩
  -- Let S = total ones counted with multiplicity over contexts.
  set S : ℕ := ∑ k : ContextIdx, ∑ i : Fin 4,
      if c (contextMembers k i) then (1 : ℕ) else 0 with hS_def
  -- Step 1: S = 9, since each context has exactly one `1`.
  have hS9 : S = 9 := by
    have hsum : S = ∑ _k : ContextIdx, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro k _; exact hc k
    rw [hsum]; decide
  -- Step 2: rewrite each cell indicator as a sum over v.
  -- (if c (members k i) then 1 else 0) = ∑ v, (if members k i = v then ind(c v) else 0)
  have hCell : ∀ (k : ContextIdx) (i : Fin 4),
      (if c (contextMembers k i) then (1 : ℕ) else 0)
        = ∑ v : VecIdx,
            if contextMembers k i = v then (if c v then (1 : ℕ) else 0) else 0 := by
    intro k i
    -- The sum has exactly one nonzero term: at v = contextMembers k i.
    rw [Finset.sum_eq_single (contextMembers k i)]
    · simp
    · intro v _ hv
      rw [if_neg hv.symm]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  -- Step 3: substitute and swap the v-sum outside.
  have hS_even : S = 2 * (∑ v : VecIdx, if c v then (1 : ℕ) else 0) := by
    -- First rewrite S into triple-nested form.
    have h1 : S = ∑ k : ContextIdx, ∑ i : Fin 4, ∑ v : VecIdx,
        if contextMembers k i = v then (if c v then (1 : ℕ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      exact hCell k i
    rw [h1]
    -- Swap v outside via two Finset.sum_comm applications.
    -- ∑ k, ∑ i, ∑ v, F = ∑ k, ∑ v, ∑ i, F   (inner swap, per k)
    rw [show (∑ k : ContextIdx, ∑ i : Fin 4, ∑ v : VecIdx,
              (if contextMembers k i = v then (if c v then (1 : ℕ) else 0) else 0))
            = ∑ k : ContextIdx, ∑ v : VecIdx, ∑ i : Fin 4,
              (if contextMembers k i = v then (if c v then (1 : ℕ) else 0) else 0) from by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm]
    -- Now: ∑ k, ∑ v, ∑ i, F. Swap k and v (outer).
    rw [Finset.sum_comm]
    -- Goal: ∑ v, ∑ k, ∑ i, F = 2 * ∑ v, ind(c v)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    -- Goal: ∑ k, ∑ i, (if k,i=v then ind(c v) else 0) = 2 * ind(c v)
    by_cases hcv : c v
    · -- ind(c v) = 1
      simp only [hcv, if_true]
      have hlem := each_vector_in_two_contexts v
      -- hlem: ∑ k, ∑ i, (if k,i = v then 1 else 0) = 2
      -- Goal after simp: ∑ k, ∑ i, (if k,i = v then 1 else 0) = 2 * 1
      rw [hlem]; rfl
    · -- ind(c v) = 0, all terms 0
      simp [hcv]
  -- Step 4: combine to get 9 = 2 * N, contradiction.
  have h2div : 2 ∣ S := ⟨_, hS_even⟩
  rw [hS9] at h2div
  omega

end KochenSpecker_en


/-!
## Connection to Free Will Theorem (Pilier 2)

The KS theorem is the combinatorial core of the SPIN axiom:
for spin-1 particles, measuring the squared spin component along
3 (or, in the 4D version here, 4) mutually compatible projectors
always yields a fixed pattern (one "1" per orthonormal basis).
If the response were a deterministic function of hidden variables,
it would define a valid {0,1}-coloring — contradicting KS.
Hence the particle's response cannot be a function of the past alone.

This connection will be formalized in Pilier 2 (FreeWillTheorem.lean),
together with the TWIN and MIN axioms.
-/

end Conway_en

/-
  Knots.Lidman — The unknotting number of 11n102 is 2
  ===================================================

  Tye Lidman (2026) proved that the unknotting number u(11n102) = 2.
  It was previously known that u(11n102) ∈ {1, 2}.

  The proof is one page but extraordinarily deep, using:
  1. Montesinos trick: branched double cover ↔ half-integral surgery
  2. Seifert fibered spaces and their plumbing descriptions
  3. Heegaard Floer homology (d-invariants, HFred)
  4. Ni-Wu formula for cosmetic surgeries
  5. Gainullin's mapping cone formula

  Reference: Lidman (2026), arXiv:2606.12431

  Epic #2874, Phase 1 (scaffolding only — sorry permanent).

  Mathlib prerequisites needed (VERY FAR):
  - 3-manifold topology (branched covers, Seifert fibered spaces)
  - Heegaard Floer homology (d-invariants, HFred)
  - Surgery on knots (Dehn surgery, integral/half-integral)
  - Plumbing diagrams for 4-manifolds
  - Némethi's algorithm for computing HF of plumbed manifolds
-/

import Knots.Basic_en
import Knots.Invariant_en
import Knots.Conway_en

/-
  English mirror of `Lidman.lean` (FR canonical). Convention EPIC #4980
  (decision ratified 2026-07-04, cf `code-style.md` paragraphe Lean i18n): distinct FR + EN sibling
  files - no inline bilingual block in a single file (Option B rejected). The module
  docstring and the theorem docstrings below differ from the FR version; the body
  signatures, proofs and tactics remain byte-identical between the two files.
-/

open Knots_en

namespace Knots_en

/-! ## 1. The knot 11n102

11n102 is a knot with 11 crossings in the KnotInfo table.
It is a Montesinos knot M(-2/3, 1/3, 2/7) with determinant 3.
-/

/-- The knot 11n102, defined by its PD-code from KnotInfo.
    Reference: KnotInfo, https://knotinfo.org (entry 11n_102, PD notation),
    fetched and hand-checked 2026-07-02: 11 crossings, 22 edge labels,
    each label 1..22 appears exactly twice.
    Classification (KnotInfo): Montesinos K(2/3;-1/3;-2/7), determinant 3. -/
def knot_11n102_diagram : KnotDiagram where
  crossings := [
    ⟨4,  2,  5,  1⟩,   -- crossing 1
    ⟨7,  12, 8,  13⟩,  -- crossing 2
    ⟨10, 3,  11, 4⟩,   -- crossing 3
    ⟨2,  11, 3,  12⟩,  -- crossing 4
    ⟨5,  14, 6,  15⟩,  -- crossing 5
    ⟨13, 6,  14, 7⟩,   -- crossing 6
    ⟨17, 20, 18, 21⟩,  -- crossing 7
    ⟨9,  19, 10, 18⟩,  -- crossing 8
    ⟨19, 9,  20, 8⟩,   -- crossing 9
    ⟨15, 22, 16, 1⟩,   -- crossing 10
    ⟨21, 16, 22, 17⟩   -- crossing 11
  ]
  numEdges := 22

def knot_11n102 : Knot where
  diagram := knot_11n102_diagram


/-! ## 2. Unknotting number bounds

KnotInfo gives u(11n102) ∈ {1, 2}. Lidman shows it is exactly 2.
-/

/-- The unknotting number of 11n102 is at most 2
(obvious from a diagram with appropriate crossing changes). -/
theorem unknotting_11n102_upper : Knot.unknottingNumber knot_11n102 ≤ 2 := by
  exact sorry
  -- Proof: exhibit 2 crossing changes that unknot the diagram
  -- Phase 3 target (once unknottingNumber is properly defined)

/-! ## 3. Lidman's theorem (statement only)

The main theorem: u(11n102) = 2, proved by contradiction.
Assume u(11n102) = 1. Then by the Montesinos trick, the branched
double cover Y of 11n102 is ±3/2-surgery on some knot J in S³.

Computing Heegaard Floer of Y (a Seifert fibered space) and comparing
d-invariants via Ni-Wu leads to a contradiction on the structure
of HFred(Y).
-/

/-- Lidman's theorem: the unknotting number of 11n102 is exactly 2. -/
theorem unknotting_11n102 : Knot.unknottingNumber knot_11n102 = 2 := by
  exact sorry
  -- Reference: Lidman (2026), arXiv:2606.12431
  --
  -- Proof sketch (contradiction from u = 1):
  --
  -- Step 1 (Montesinos trick):
  --   If u(11n102) = 1, then the branched double cover Y is
  --   half-integral surgery ±3/2 on some knot J in S³.
  --   Reference: Montesinos (1973), Bol. Soc. Mat. Mexicana
  --
  -- Step 2 (Seifert structure):
  --   Y = S²(1; 1/3, 1/3, 2/7) is a Seifert fibered space.
  --   The plumbing bounding Y is positive-definite.
  --   Reference: Montesinos (1973)
  --
  -- Step 3 (Heegaard Floer computation):
  --   Using Némethi's algorithm: HFred has two spinc structures
  --   with HFred = 0 and one with HFred = F₂.
  --   d-invariants: d = 1/6 (×2) and d = -1/2 (×1).
  --   Reference: Némethi (2005),Geom. Topol.
  --             Ozsváth-Szabó (2003),Geom. Topol.
  --
  -- Step 4 (Ni-Wu comparison):
  --   The mod 2 d-invariants match +3/2-surgery on the unknot,
  --   so Y = +3/2(J) and V_s(J) = H_s(J) = 0 for all s ≥ 0.
  --   Reference: Ni-Wu (2015),J. Reine Angew. Math.
  --
  -- Step 5 (Gainullin's formula):
  --   HFred(Y, s_i) ≅ A^{red}_{i,3/2} where
  --   A^{red}_{i,3/2} = ⊕_k Q_{⌊(i+3k)/2⌋}
  --   Each Q_s appears in TWO of the three A^{red}_{i,3/2}.
  --   But only ONE of the three HFred(Y, s_i) is non-zero.
  --   Contradiction: impossible for exactly one to be non-zero.
  --   Reference: Gainullin (2017),Algebr. Geom. Topol.
  --
  -- Mathlib prerequisites (ALL missing):
  --   - 3-manifolds, branched double covers
  --   - Seifert fibered spaces
  --   - Heegaard Floer homology (d-invariants, HFred)
  --   - Surgery on knots
  --   - Plumbing diagrams for 4-manifolds
  --   - Ni-Wu formula
  --   - Gainullin's mapping cone formula
  --
  -- Estimated difficulty: **decades** away from formalization.
  -- This sorry is effectively permanent.

/-! ## 4. Appendix: Alexander polynomial of 11n102 (kernel computation)

The unknotting certificate of §2 is inexpressible under the current connected
Reidemeister machinery (append-only moves, fresh tail labels — diagnosis
posted on #2874); the Alexander polynomial, on the other hand, is computable
by the lake's kernel machinery, following the same pattern as
`conway_trivial_alexander` and `KT_trivial_alexander` (Conway.lean):
deterministic Gaussian elimination of the designated 10×10 minor over ℤ[t],
by transvections only (34 operations, rows and columns, determinant
preserved exactly — no scaling, no signed swaps).

Designated value: Δ(t) = 2t⁷ − t⁶ − t⁵ + t³. Classical check (corollary
below): |Δ(−1)| = 3, the knot determinant reported by KnotInfo.
-/

/-- Control: the arc partition of the 11n102 PD code — 11 arcs covering the
22 edges (non-degeneracy condition of the Alexander minor: the guard
`arcs'.length = rest.length + 1` of `alexanderPolynomialAux` goes through). -/
theorem knot_11n102_arcPartition :
    arcPartition knot_11n102_diagram =
      [[5], [10], [3, 4], [11, 12, 13], [14, 15], [6, 7], [20, 21], [18, 19],
       [8, 9], [22, 1, 2], [16, 17]] := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 32000000 in
/-- Alexander polynomial of 11n102 — designated value of the 10×10 minor
over ℤ[t], by deterministic Gaussian elimination through integral
transvections (rows and columns), determinant preserved exactly: the final
diagonal product reads (−t)·1·(−1)·1·(−1)·1·(−1)·(−t)·(−1)·(2t⁵ − t⁴ − t³ + t)
= 2t⁷ − t⁶ − t⁵ + t³. -/
theorem alexander_knot_11n102 :
    alexanderPolynomial knot_11n102 =
      (0 : Polynomial ℤ) + 2 * Polynomial.X ^ 7 - Polynomial.X ^ 6
        - Polynomial.X ^ 5 + Polynomial.X ^ 3 := by
  have hp := knot_11n102_arcPartition
  simp only [alexanderPolynomial, alexanderPolynomialAux, knot_11n102, hp]
  simp only [knot_11n102_diagram]
  have hlen : ([[5], [10], [3, 4], [11, 12, 13], [14, 15], [6, 7], [20, 21],
      [18, 19], [8, 9], [22, 1, 2], [16, 17]] : List (List Nat)).length =
      ([⟨7, 12, 8, 13⟩, ⟨10, 3, 11, 4⟩, ⟨2, 11, 3, 12⟩, ⟨5, 14, 6, 15⟩,
      ⟨13, 6, 14, 7⟩, ⟨17, 20, 18, 21⟩, ⟨9, 19, 10, 18⟩, ⟨19, 9, 20, 8⟩,
      ⟨15, 22, 16, 1⟩, ⟨21, 16, 22, 17⟩] : List PDCrossing).length + 1 := by
    decide
  rw [if_pos hlen]
  show (Matrix.of fun (i j : Fin 10) => alexanderEntry
        ([⟨7, 12, 8, 13⟩, ⟨10, 3, 11, 4⟩, ⟨2, 11, 3, 12⟩, ⟨5, 14, 6, 15⟩,
      ⟨13, 6, 14, 7⟩, ⟨17, 20, 18, 21⟩, ⟨9, 19, 10, 18⟩, ⟨19, 9, 20, 8⟩,
      ⟨15, 22, 16, 1⟩, ⟨21, 16, 22, 17⟩][i.1]?.getD ⟨1, 1, 1, 1⟩)
        ([[5], [10], [3, 4], [11, 12, 13], [14, 15], [6, 7], [20, 21],
      [18, 19], [8, 9], [22, 1, 2], [16, 17]][j.1]?.getD [])).det =
      (0 : Polynomial ℤ) + 2 * Polynomial.X ^ 7 - Polynomial.X ^ 6
        - Polynomial.X ^ 5 + Polynomial.X ^ 3
  set A0 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h0
  have hM0 : (Matrix.of fun (i j : Fin 10) => alexanderEntry
        ([⟨7, 12, 8, 13⟩, ⟨10, 3, 11, 4⟩, ⟨2, 11, 3, 12⟩, ⟨5, 14, 6, 15⟩,
      ⟨13, 6, 14, 7⟩, ⟨17, 20, 18, 21⟩, ⟨9, 19, 10, 18⟩, ⟨19, 9, 20, 8⟩,
      ⟨15, 22, 16, 1⟩, ⟨21, 16, 22, 17⟩][i.1]?.getD ⟨1, 1, 1, 1⟩)
        ([[5], [10], [3, 4], [11, 12, 13], [14, 15], [6, 7], [20, 21],
      [18, 19], [8, 9], [22, 1, 2], [16, 17]][j.1]?.getD [])) = A0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp (config := { decide := true }) [Matrix.of_apply,
        alexanderEntry, h0] <;>
      first
      | rfl
      | ring
  rw [hM0]
  set A1 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h1
  have e1 : A1 = A0.updateRow 3 (A0 3 + (1 : Polynomial ℤ) • A0 0) := by
    rw [h1, h0]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d1 : A1.det = A0.det := by
    rw [e1, Matrix.det_updateRow_add_smul_self A0 (by decide : ((3 : Fin 10) ≠ 0)) (1 : Polynomial ℤ)]
  set A2 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h2
  have e2 : A2 = A1.updateRow 0 (A1 0 + (-1 : Polynomial ℤ) • A1 3) := by
    rw [h2, h1]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d2 : A2.det = A1.det := by
    rw [e2, Matrix.det_updateRow_add_smul_self A1 (by decide : ((0 : Fin 10) ≠ 3)) (-1 : Polynomial ℤ)]
  set A3 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h3
  have e3 : A3 = A2.updateRow 3 (A2 3 + (1 : Polynomial ℤ) • A2 0) := by
    rw [h3, h2]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d3 : A3.det = A2.det := by
    rw [e3, Matrix.det_updateRow_add_smul_self A2 (by decide : ((3 : Fin 10) ≠ 0)) (1 : Polynomial ℤ)]
  set A4 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h4
  have e4 : A4 = A3.updateRow 6 (A3 6 + (1 : Polynomial ℤ) • A3 1) := by
    rw [h4, h3]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d4 : A4.det = A3.det := by
    rw [e4, Matrix.det_updateRow_add_smul_self A3 (by decide : ((6 : Fin 10) ≠ 1)) (1 : Polynomial ℤ)]
  set A5 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h5
  have e5 : A5 = A4.updateRow 1 (A4 1 + (-1 : Polynomial ℤ) • A4 6) := by
    rw [h5, h4]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d5 : A5.det = A4.det := by
    rw [e5, Matrix.det_updateRow_add_smul_self A4 (by decide : ((1 : Fin 10) ≠ 6)) (-1 : Polynomial ℤ)]
  set A6 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h6
  have e6 : A6 = A5.updateRow 6 (A5 6 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A5 1) := by
    rw [h6, h5]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d6 : A6.det = A5.det := by
    rw [e6, Matrix.det_updateRow_add_smul_self A5 (by decide : ((6 : Fin 10) ≠ 1)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A7 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h7
  have e7 : A7 = A6.updateRow 6 (A6 6 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A6 2) := by
    rw [h7, h6]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d7 : A7.det = A6.det := by
    rw [e7, Matrix.det_updateRow_add_smul_self A6 (by decide : ((6 : Fin 10) ≠ 2)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A8 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h8
  have e8 : A8 = A7.updateCol 8 (fun r => A7 r 8 + (1 : Polynomial ℤ) • A7 r 3) := by
    rw [h8, h7]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d8 : A8.det = A7.det := by
    rw [e8, Matrix.det_updateCol_add_smul_self A7 (by decide : ((8 : Fin 10) ≠ 3)) (1 : Polynomial ℤ)]
  set A9 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h9
  have e9 : A9 = A8.updateCol 3 (fun r => A8 r 3 + (-1 : Polynomial ℤ) • A8 r 8) := by
    rw [h9, h8]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d9 : A9.det = A8.det := by
    rw [e9, Matrix.det_updateCol_add_smul_self A8 (by decide : ((3 : Fin 10) ≠ 8)) (-1 : Polynomial ℤ)]
  set A10 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h10
  have e10 : A10 = A9.updateCol 8 (fun r => A9 r 8 + (1 : Polynomial ℤ) • A9 r 3) := by
    rw [h10, h9]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d10 : A10.det = A9.det := by
    rw [e10, Matrix.det_updateCol_add_smul_self A9 (by decide : ((8 : Fin 10) ≠ 3)) (1 : Polynomial ℤ)]
  set A11 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h11
  have e11 : A11 = A10.updateRow 6 (A10 6 + ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ) • A10 3) := by
    rw [h11, h10]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d11 : A11.det = A10.det := by
    rw [e11, Matrix.det_updateRow_add_smul_self A10 (by decide : ((6 : Fin 10) ≠ 3)) ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ)]
  set A12 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h12
  have e12 : A12 = A11.updateRow 7 (A11 7 + ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A11 3) := by
    rw [h12, h11]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d12 : A12.det = A11.det := by
    rw [e12, Matrix.det_updateRow_add_smul_self A11 (by decide : ((7 : Fin 10) ≠ 3)) ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A13 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h13
  have e13 : A13 = A12.updateRow 8 (A12 8 + ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ) • A12 4) := by
    rw [h13, h12]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d13 : A13.det = A12.det := by
    rw [e13, Matrix.det_updateRow_add_smul_self A12 (by decide : ((8 : Fin 10) ≠ 4)) ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  set A14 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h14
  have e14 : A14 = A13.updateCol 7 (fun r => A13 r 7 + (1 : Polynomial ℤ) • A13 r 5) := by
    rw [h14, h13]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d14 : A14.det = A13.det := by
    rw [e14, Matrix.det_updateCol_add_smul_self A13 (by decide : ((7 : Fin 10) ≠ 5)) (1 : Polynomial ℤ)]
  set A15 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h15
  have e15 : A15 = A14.updateCol 5 (fun r => A14 r 5 + (-1 : Polynomial ℤ) • A14 r 7) := by
    rw [h15, h14]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d15 : A15.det = A14.det := by
    rw [e15, Matrix.det_updateCol_add_smul_self A14 (by decide : ((5 : Fin 10) ≠ 7)) (-1 : Polynomial ℤ)]
  set A16 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h16
  have e16 : A16 = A15.updateCol 7 (fun r => A15 r 7 + (1 : Polynomial ℤ) • A15 r 5) := by
    rw [h16, h15]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d16 : A16.det = A15.det := by
    rw [e16, Matrix.det_updateCol_add_smul_self A15 (by decide : ((7 : Fin 10) ≠ 5)) (1 : Polynomial ℤ)]
  set A17 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h17
  have e17 : A17 = A16.updateRow 6 (A16 6 + ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ) • A16 5) := by
    rw [h17, h16]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d17 : A17.det = A16.det := by
    rw [e17, Matrix.det_updateRow_add_smul_self A16 (by decide : ((6 : Fin 10) ≠ 5)) ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)]
  set A18 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ)]
  ] with h18
  have e18 : A18 = A17.updateRow 7 (A17 7 + ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ) • A17 5) := by
    rw [h18, h17]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d18 : A18.det = A17.det := by
    rw [e18, Matrix.det_updateRow_add_smul_self A17 (by decide : ((7 : Fin 10) ≠ 5)) ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  set A19 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - 3 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h19
  have e19 : A19 = A18.updateCol 9 (fun r => A18 r 9 + (1 : Polynomial ℤ) • A18 r 6) := by
    rw [h19, h18]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d19 : A19.det = A18.det := by
    rw [e19, Matrix.det_updateCol_add_smul_self A18 (by decide : ((9 : Fin 10) ≠ 6)) (1 : Polynomial ℤ)]
  set A20 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - 3 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h20
  have e20 : A20 = A19.updateCol 6 (fun r => A19 r 6 + (-1 : Polynomial ℤ) • A19 r 9) := by
    rw [h20, h19]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d20 : A20.det = A19.det := by
    rw [e20, Matrix.det_updateCol_add_smul_self A19 (by decide : ((6 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A21 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  ] with h21
  have e21 : A21 = A20.updateCol 9 (fun r => A20 r 9 + (1 : Polynomial ℤ) • A20 r 6) := by
    rw [h21, h20]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d21 : A21.det = A20.det := by
    rw [e21, Matrix.det_updateCol_add_smul_self A20 (by decide : ((9 : Fin 10) ≠ 6)) (1 : Polynomial ℤ)]
  set A22 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)]
  ] with h22
  have e22 : A22 = A21.updateRow 9 (A21 9 + (1 : Polynomial ℤ) • A21 6) := by
    rw [h22, h21]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d22 : A22.det = A21.det := by
    rw [e22, Matrix.det_updateRow_add_smul_self A21 (by decide : ((9 : Fin 10) ≠ 6)) (1 : Polynomial ℤ)]
  set A23 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)]
  ] with h23
  have e23 : A23 = A22.updateRow 6 (A22 6 + (-1 : Polynomial ℤ) • A22 9) := by
    rw [h23, h22]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d23 : A23.det = A22.det := by
    rw [e23, Matrix.det_updateRow_add_smul_self A22 (by decide : ((6 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A24 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)]
  ] with h24
  have e24 : A24 = A23.updateRow 9 (A23 9 + (1 : Polynomial ℤ) • A23 6) := by
    rw [h24, h23]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d24 : A24.det = A23.det := by
    rw [e24, Matrix.det_updateRow_add_smul_self A23 (by decide : ((9 : Fin 10) ≠ 6)) (1 : Polynomial ℤ)]
  set A25 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)]
  ] with h25
  have e25 : A25 = A24.updateRow 8 (A24 8 + ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ) • A24 6) := by
    rw [h25, h24]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d25 : A25.det = A24.det := by
    rw [e25, Matrix.det_updateRow_add_smul_self A24 (by decide : ((8 : Fin 10) ≠ 6)) ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  set A26 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h26
  have e26 : A26 = A25.updateRow 9 (A25 9 + ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ) • A25 6) := by
    rw [h26, h25]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d26 : A26.det = A25.det := by
    rw [e26, Matrix.det_updateRow_add_smul_self A25 (by decide : ((9 : Fin 10) ≠ 6)) ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ)]
  set A27 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - 2 * Polynomial.X + 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)]
  ] with h27
  have e27 : A27 = A26.updateRow 8 (A26 8 + (-1 : Polynomial ℤ) • A26 7) := by
    rw [h27, h26]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d27 : A27.det = A26.det := by
    rw [e27, Matrix.det_updateRow_add_smul_self A26 (by decide : ((8 : Fin 10) ≠ 7)) (-1 : Polynomial ℤ)]
  set A28 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((2 : Polynomial ℤ) - 5 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)]
  ] with h28
  have e28 : A28 = A27.updateRow 9 (A27 9 + ((2 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ) • A27 7) := by
    rw [h28, h27]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d28 : A28.det = A27.det := by
    rw [e28, Matrix.det_updateRow_add_smul_self A27 (by decide : ((9 : Fin 10) ≠ 7)) ((2 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)]
  set A29 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((2 : Polynomial ℤ) - 5 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℤ), ((-2 : Polynomial ℤ) + 2 * Polynomial.X - 2 * Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ)]
  ] with h29
  have e29 : A29 = A28.updateRow 7 (A28 7 + (-1 : Polynomial ℤ) • A28 9) := by
    rw [h29, h28]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d29 : A29.det = A28.det := by
    rw [e29, Matrix.det_updateRow_add_smul_self A28 (by decide : ((7 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A30 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ), (1 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - 3 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X + Polynomial.X ^ 2 - Polynomial.X ^ 4 : Polynomial ℤ)]
  ] with h30
  have e30 : A30 = A29.updateRow 9 (A29 9 + ((2 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ) • A29 7) := by
    rw [h30, h29]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d30 : A30.det = A29.det := by
    rw [e30, Matrix.det_updateRow_add_smul_self A29 (by decide : ((9 : Fin 10) ≠ 7)) ((2 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)]
  set A31 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X + Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - 3 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ)]
  ] with h31
  have e31 : A31 = A30.updateCol 9 (fun r => A30 r 9 + (1 : Polynomial ℤ) • A30 r 8) := by
    rw [h31, h30]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d31 : A31.det = A30.det := by
    rw [e31, Matrix.det_updateCol_add_smul_self A30 (by decide : ((9 : Fin 10) ≠ 8)) (1 : Polynomial ℤ)]
  set A32 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X + Polynomial.X ^ 3 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 - Polynomial.X ^ 4 : Polynomial ℤ)]
  ] with h32
  have e32 : A32 = A31.updateCol 8 (fun r => A31 r 8 + (-1 : Polynomial ℤ) • A31 r 9) := by
    rw [h32, h31]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d32 : A32.det = A31.det := by
    rw [e32, Matrix.det_updateCol_add_smul_self A31 (by decide : ((8 : Fin 10) ≠ 9)) (-1 : Polynomial ℤ)]
  set A33 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 4 : Polynomial ℤ), ((0 : Polynomial ℤ) + 2 * Polynomial.X - 3 * Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ)]
  ] with h33
  have e33 : A33 = A32.updateCol 9 (fun r => A32 r 9 + (1 : Polynomial ℤ) • A32 r 8) := by
    rw [h33, h32]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateCol_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d33 : A33.det = A32.det := by
    rw [e33, Matrix.det_updateCol_add_smul_self A32 (by decide : ((9 : Fin 10) ≠ 8)) (1 : Polynomial ℤ)]
  set A34 : Matrix (Fin 10) (Fin 10) (Polynomial ℤ) := Matrix.of ![
    ![((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((1 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (1 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X : Polynomial ℤ), (0 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) - Polynomial.X : Polynomial ℤ), ((-1 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 3 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (-1 : Polynomial ℤ), ((-1 : Polynomial ℤ) + 2 * Polynomial.X : Polynomial ℤ)],
    ![(0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), (0 : Polynomial ℤ), ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 3 - Polynomial.X ^ 4 + 2 * Polynomial.X ^ 5 : Polynomial ℤ)]
  ] with h34
  have e34 : A34 = A33.updateRow 9 (A33 9 + ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 4 : Polynomial ℤ) • A33 8) := by
    rw [h34, h33]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.updateRow_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;>
      first
      | rfl
      | ring
  have d34 : A34.det = A33.det := by
    rw [e34, Matrix.det_updateRow_add_smul_self A33 (by decide : ((9 : Fin 10) ≠ 8)) ((0 : Polynomial ℤ) + Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 4 : Polynomial ℤ)]
  have hchain : A34.det = A0.det := by
    rw [d34, d33, d32, d31, d30, d29, d28, d27, d26, d25, d24, d23, d22, d21, d20, d19, d18, d17, d16, d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hT : A34.BlockTriangular id := by
    intro i j hij
    rw [h34]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | simp [Matrix.of_apply, Matrix.updateRow_apply, Matrix.updateCol_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hdiag : (∏ i, A34 i i) =
      (0 : Polynomial ℤ) + 2 * Polynomial.X ^ 7 - Polynomial.X ^ 6
        - Polynomial.X ^ 5 + Polynomial.X ^ 3 := by
    rw [h34]
    simp only [Fin.prod_univ_succ, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.isValue]
    have htail : ∀ g : Fin 0 → Polynomial ℤ, (∏ i, g i) = 1 := fun g =>
      Finset.prod_eq_one (fun x _ => Fin.elim0 x)
    rw [htail _]
    ring
  rw [← hchain, Matrix.det_of_upperTriangular hT]
  exact hdiag

/-- Corollary: evaluation at −1 recovers (up to sign) the knot determinant,
3 — matching KnotInfo (header §1, "determinant 3"). -/
theorem alexander_11n102_eval_neg_one :
    (alexanderPolynomial knot_11n102).eval (-1 : ℤ) = -3 := by
  rw [alexander_knot_11n102]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X]
  norm_num

end Knots_en

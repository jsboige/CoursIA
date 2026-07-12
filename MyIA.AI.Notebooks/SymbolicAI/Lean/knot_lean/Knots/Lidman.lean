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

import Knots.Basic
import Knots.Invariant

namespace Knots

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
  hwell := by trivial  -- TODO Phase 2: proper well-formedness check

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

end Knots

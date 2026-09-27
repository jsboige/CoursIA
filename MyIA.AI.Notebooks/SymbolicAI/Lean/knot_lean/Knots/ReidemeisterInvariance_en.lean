/-
Knots.ReidemeisterInvariance — Invariance of invariants under Reidemeister moves
================================================================================

Home of the invariance theorem: `alexanderPolynomialSigned` is invariant under
the three Reidemeister moves (issue #16650, tranche 3 of the Alexander socle,
strategy `docs/lean/alexander-strategy/c652-reidemeister-invariance.md`).

Why a separate module: the theorem crosses `Reidemeister3Connected`
(`Knots.Reidemeister`) and `alexanderPolynomialSigned` (`Knots.Conway`).
`Knots.Conway` imports `Knots.Invariant`, which imports `Knots.Reidemeister` —
so importing `Knots.Conway` suffices to see both, and the converse would be a
cycle. This module is where the two theories meet.

English mirror of `ReidemeisterInvariance.lean` (FR canonical). Convention EPIC
#4980 (ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct FR + EN
sibling files — no inline bilingual block. The module docstring and the theorem
docstrings below differ from the FR version; the body signatures, proofs and
tactics remain byte-identical between the two files.
-/

import Knots.Conway_en

namespace Knots_en

/-! ## 1. The `i = 0` / `i ≥ 1` split (a point the strategy misses)

Strategy c652 (§4.1) presents R3 as "trivial by reindexation". That holds **under
a condition it does not state**: that the triangle lies entirely outside the row
the designated minor deletes.

`alexanderPolynomialSigned` deletes the **first** row (`rest` = tail of
`crossings`) and the last column of the minor. Hence:

* **`i ≥ 1`** — the three rewritten rows of the triangle lie in the body of the
  matrix; invariance is a reindexation argument: the surgery changes neither the
  number of crossings nor the number of edges, and the arc partition is
  preserved (section 2 below). The minor is unchanged up to the transport of
  columns.
* **`i = 0`** — row 0 carries a vertex of the triangle, and that is precisely
  the row the designated minor **deletes**. Reindexation no longer suffices: the
  minor changes shape (coefficients leave the triangle's columns for others),
  and invariance can only be read up to a **unit** `±t^k` — this is the
  determinantal argument of sections 4.2-4.3 of the strategy (non-shared column,
  rank of the augmented minor).

The two cases are therefore of different nature and must be distinct theorems.
Conflating them would make `i = 0` look like a missing proof when it is in fact
the case where the designated minor genuinely changes shape.

## 2. The arc-partition preservation obligation

The reindexation argument (`i ≥ 1`) rests on a premise the strategy **assumes
without proving**: `arcPartition` is preserved by the surgery.

The general statement requires: the connected R3 surgery rewrites the
`(e2, e4)` pairs of the triangle's three crossings (cf `Conway_en.lean:350-354`,
`pairs := d.crossings.map (fun c => (c.e2, c.e4))`). On the lake's witness
(`reidemeister3Connected_satisfiable`), those pairs, taken as an unordered
multiset (`mergePair` is symmetric in its two arguments), **coincide** between
X and Y — the partition is therefore preserved trivially, and `decide` at the
kernel suffices to discharge the theorem.

This witness alone does not, however, ground the general preservation: a
minimal counterexample where the triangle's `(e2, e4)` pairs genuinely differ
between X and Y remains to be exhibited. This is the first lock of the
tranche, before any reindexation argument.
-/

/-! ## 3. Control: the R3 witness's arc partition is preserved

The witness is that of `reidemeister3Connected_satisfiable` (literals copied
verbatim): both diagrams are well formed (`decide` on `wf` in the lake), and
their arc partition — 5 classes for 10 edges — is **the same** on both sides of
the surgery. This is the **trivial control** of section 2: on this witness,
the triangle's `(e2, e4)` pairs coincide as a multiset between X and Y — the
preservation is vacuous. A counterexample where they differ remains to be
exhibited to ground the general preservation.
-/

/-- Control of tranche 3 (step 1): on the witness pair of the connected R3 move,
    the surgery preserves `arcPartition`. On this witness, the triangle's
    `(e2, e4)` pairs coincide as a multiset between X and Y, so the preservation
    is trivial; the general form (on diagrams where the triangle's pairs differ)
    remains to be proved. -/
theorem reidemeister3Connected_arcPartition_witness :
    arcPartition
        { crossings := [⟨1, 2, 7, 8⟩, ⟨3, 7, 9, 4⟩, ⟨9, 8, 5, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 }
      = arcPartition
        { crossings := [⟨3, 4, 9, 7⟩, ⟨9, 2, 5, 8⟩, ⟨7, 8, 1, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 } := by
  decide

/-! ## 4. Negative control: the designated minor collapses on the Y witness

Section 3 establishes the **first premise** of the reindexation argument (the
arc partition is preserved). The expected **conclusion** control — the signed
polynomial of the witness is the same on both sides — is **refuted on this
witness**, and that is framing information, not a proof failure:

* on the X side, the designated minor is `t³ - t²` (all-positive chirality);
* on the Y side, the designated minor is **identically zero** — and the Python
  probe faithful to the construction (validated against the kernel values of
  the signed `trefoil` and `figureEight`) measures the same nullity for each
  of the five deletable columns and each of the 32 chirality assignments.

The cause reads off the matrix rows: the surgery rewrites `(9, 8, 5, 6)` into
`(7, 8, 1, 6)`, whose non-singleton labels (`7`, `8`, `6`) all fall into the
witness's big class — its row, like the kink row `(1, 2, 10, 10)` (an exact
R1 kink: `e3 = e4`), now only touches the singleton arc column `{1}` and the
deleted big-class column. Two proportional rows: the rank drops to 3 and
every `4 × 4` minor vanishes.

The classical "every `(n-1) × (n-1)` minor of the Alexander matrix equals
`± t^k · Δ`" assumes the matrix has rank `n - 1`; the kink adds a relation,
and the designated normalization (first row and last column deleted,
**fixed**) does not survive the surgery. Consequence for section 1: the
reindexation argument of the `i ≥ 1` case must either restrict to kink-free
diagrams or make the deleted (row, column) pair adaptive.
-/

/-- Generic 4×4 determinant, same spirit as `det_two_aux` / `det_three_aux`
    from `Conway.lean`: Laplace expansion along the first column, the 3×3
    minors being handled by `det_three_aux`. -/
theorem det_four_aux (A : Matrix (Fin 4) (Fin 4) (Polynomial ℤ)) :
    A.det = A 0 0 * (A.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det
          - A 1 0 * (A.submatrix (Fin.succAbove 1) (Fin.succAbove 0)).det
          + A 2 0 * (A.submatrix (Fin.succAbove 2) (Fin.succAbove 0)).det
          - A 3 0 * (A.submatrix (Fin.succAbove 3) (Fin.succAbove 0)).det := by
  rw [Matrix.det_succ_column_zero]
  simp (config := { decide := true }) [Fin.sum_univ_succ]
  simp (config := { decide := true }) [det_three_aux, Matrix.submatrix_apply,
    Fin.succAbove]
  ring

/-- Tranche 3 control: on the X side, the designated minor of the signed
    polynomial (all-positive chirality) equals `t³ - t²` — it is not
    degenerate. This is the positive counterpart of the negative control
    below: it is the surgery that collapses the minor, not a prior
    degeneracy. -/
theorem reidemeister3Connected_alexanderSigned_witness_X :
    alexanderPolynomialSigned
        { crossings := [⟨1, 2, 7, 8⟩, ⟨3, 7, 9, 4⟩, ⟨9, 8, 5, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 }
        [true, true, true, true, true]
      = Polynomial.X ^ 3 - Polynomial.X ^ 2 := by
  simp only [alexanderPolynomialSigned]
  simp (config := { decide := true })
  rw [det_four_aux]
  simp only [det_three_aux]
  simp only [Matrix.submatrix_apply, Fin.succAbove, Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry,
    alexanderEntryNeg]
  ring

/-- Tranche 3 negative control: on the Y side, **the same designated minor is
    identically zero** — the witness's R3 surgery aligns the rewritten
    crossing's row `(7, 8, 1, 6)` with the kink row `(1, 2, 10, 10)` (both now
    only touch the singleton arc `{1}` and the deleted big class), the rank
    drops to 3 and the determinant vanishes (probe: null for all five
    deletable columns and all 32 chirality assignments). The designated
    normalization does not survive the surgery on a kink-carrying witness —
    cf section 4 of the module. -/
theorem reidemeister3Connected_alexanderSigned_witness_Y_zero :
    alexanderPolynomialSigned
        { crossings := [⟨3, 4, 9, 7⟩, ⟨9, 2, 5, 8⟩, ⟨7, 8, 1, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 }
        [true, true, true, true, true]
      = 0 := by
  simp only [alexanderPolynomialSigned]
  simp (config := { decide := true })
  rw [det_four_aux]
  simp only [det_three_aux]
  simp only [Matrix.submatrix_apply, Fin.succAbove, Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry,
    alexanderEntryNeg]

end Knots_en

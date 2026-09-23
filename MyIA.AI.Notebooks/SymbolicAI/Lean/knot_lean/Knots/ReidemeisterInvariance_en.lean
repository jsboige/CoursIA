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

end Knots_en

/-
  Knots.FigureEight_en — Invariants of the figure-eight knot on its planar PD code (EN sibling)
  ==========================================================================================

  English sibling of `Knots.FigureEight.lean` per the i18n convention #4980
  (sibling pair: this file carries the English documentation strings; the
  code — theorem statements, proofs, tactic blocks — is byte-identical to
  the FR canonical file after `_en` suffix collapsing).

  This module proves, on the planar PD code `figureEightPlanarDiagram`
  (KnotAtlas, defined in `Knots.Jones_en`):

  1. **Signed Alexander polynomial, classical up to a unit**: with the sign
     vector read off by `crossingSign` (two negative crossings then two
     positive ones, zero writhe), the designated minor of the signed
     Alexander matrix evaluates to exactly `-t * (t^2 - 3*t + 1)` — the
     classical polynomial of 4_1 up to the unit `-t`
     (`alexander_figureEightPlanar_classical` exhibits the unit). The
     opposite sign vector (the mirror diagram) yields `-(t^2 - 3*t + 1)`,
     the same unit class, as amphichirality demands.
  2. **Determinant 5**: `det(4_1) = |Δ(-1)| = 5`, both on the signed value
     (`alexander_figureEightPlanar_eval_neg_one`) and on the unsigned one
     (`alexander_figureEightPlanar_unsigned_eval_neg_one`).
  3. **Non-tricolorability**: `¬ IsTricolorable figureEightPlanarDiagram`
     (finite enumeration, kernel `decide`) — the determinant 5, not
     divisible by 3, rules out Fox 3-colorability.
  4. **Diagram crossing count: 4** — under the PROVISIONAL Phase 3
     definition of `Knot.crossingNumber` (see the limitation below).

  ## Why a dedicated module for the planar code

  Since the canonicalisation of #17595 (PR #18272), the canonical
  `figureEightDiagram` of `Knots.Basic_en` itself carries the KnotAtlas
  planar code: `figureEightDiagram` and `figureEightPlanarDiagram` now
  designate the same planar diagram. The classical values of the
  figure-eight knot are read off this planar code, already used by
  `bracket_figureEightPlanarDiagram` and
  `jones_figureEightPlanarDiagram`. This module closes the bracket / Jones
  / Alexander trilogy on the same planar representative, and adds
  tricolorability on it.

  ## Limitations (scope honesty)

  - **No Reidemeister invariance**: as documented in `Knots.Conway_en`,
    `alexanderPolynomialSigned` is a function of the designated diagram;
    invariance under Reidemeister moves is NOT proven in this lake. The
    theorems below are computations on the designated representative, whose
    values coincide with the classical values of the knot 4_1.
  - **NO claim of topological minimal crossing number**:
    `figureEightPlanar_crossingNumber_provisional` carries the PROVISIONAL
    Phase 3 definition of `Knot.crossingNumber` (crossing count of the
    designated diagram, an UPPER bound on the topological minimum, cf the
    docstring of `Knot.crossingNumber` in `Knots.Basic_en`). It does NOT
    establish that the topological minimum of the figure-eight knot is 4 —
    that would require the classification of knots with ≤ 3 crossings, out
    of reach for this lake.

  DEEP subgrain of EPIC #2874, lane myia-po-2025:CoursIA.
-/

import Knots.Conway_en
import Knots.Jones_en

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Knots_en

/-! ## 1. Crossing signs of the planar code

`crossingSign` (defined in `Knots.Jones_en`) reads the sign of each crossing
off the PD code labelling: positive if the over-strand runs from `e2` to
`e4` (`e4 = nextEdge n e2`), negative if it runs from `e4` to `e2`. On the
planar code the four crossings split as two negative then two positive —
zero writhe, already established by `writhe_figureEightPlanarDiagram` in
`Knots.Jones_en`, the expected signature of an alternating diagram of an
amphichiral knot. -/

/-- The signs read off by `crossingSign` on the planar code: `[-1, -1, 1, 1]`.
This vector grounds the Bool list parallel to the crossings in
`alexander_figureEightPlanar_signed` below (`false` = negative). -/
theorem crossingSigns_figureEightPlanarDiagram :
    (figureEightPlanarDiagram.crossings.map
      (crossingSign figureEightPlanarDiagram.numEdges)) = [-1, -1, 1, 1] := by
  decide

/-! ## 2. Signed Alexander polynomial: classical up to a unit -/

/-- **Signed Alexander of the planar figure-eight code.** With the sign
vector read off by `crossingSign` (`[-1, -1, 1, 1]`, the theorem above — the
first crossing's sign is unused, its row is eliminated by the designated
minor), the minor yields exactly `-t * (t^2 - 3*t + 1)` — the classical
polynomial `Δ(t) = t² − 3t + 1` of 4_1 up to the unit `−t`. -/
theorem alexander_figureEightPlanar_signed :
    alexanderPolynomialSigned figureEightPlanarDiagram [false, false, true, true]
      = -(Polynomial.X) * (Polynomial.X ^ 2 - 3 * Polynomial.X + 1) := by
  simp only [alexanderPolynomialSigned, figureEightPlanarDiagram]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry, alexanderEntryNeg]
  ring

/-- **Classical up to a unit, existential form**: the Alexander polynomial
of a knot is only defined up to a unit `±t^k` (Alexander 1928); the
designated value above is `ε · t^k · (t² − 3t + 1)` for `k = 1`, `ε = −1`,
exhibited here. -/
theorem alexander_figureEightPlanar_classical :
    ∃ (k : ℕ) (ε : ℤ), ε * ε = 1 ∧
      alexanderPolynomialSigned figureEightPlanarDiagram [false, false, true, true]
        = Polynomial.C ε * Polynomial.X ^ k * (Polynomial.X ^ 2 - 3 * Polynomial.X + 1) := by
  refine ⟨1, -1, by norm_num, ?_⟩
  rw [alexander_figureEightPlanar_signed]
  have hC : (Polynomial.C (-1 : ℤ) : Polynomial ℤ) = -1 := by simp
  rw [hC]
  ring

/-- The opposite sign vector (the mirror diagram) yields
`-(t^2 - 3*t + 1)` — the same unit class as the `crossingSign` vector, as
amphichirality of the figure-eight knot demands (the two mirror diagrams
represent the same knot). Cf `alexander_figureEight_signed_mirror` in
`Knots.Conway_en` for the same fact on the DT code. -/
theorem alexander_figureEightPlanar_signed_mirror :
    alexanderPolynomialSigned figureEightPlanarDiagram [true, true, false, false]
      = -(Polynomial.X ^ 2 - 3 * Polynomial.X + 1) := by
  simp only [alexanderPolynomialSigned, figureEightPlanarDiagram]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry, alexanderEntryNeg]
  ring

/-! ## 3. Determinant 5 -/

/-- **Determinant of the figure-eight knot: 5.** For a knot,
`det = |Δ(−1)|`; the signed value of the planar code evaluates to exactly
`5` at `t = −1` (the unit `−t` of the designated normalisation does not
affect this reading: `|−(−1) · 5| = 5`). -/
theorem alexander_figureEightPlanar_eval_neg_one :
    (alexanderPolynomialSigned figureEightPlanarDiagram [false, false, true, true]).eval (-1)
      = 5 := by
  rw [alexander_figureEightPlanar_signed]
  simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_X_pow]
  norm_num

/-- **Cross-check: the unsigned version on the planar code** yields
`t^3 - 2*t^2 + 2*t` — the same chirality pathology as on the DT code
(`alexander_figureEight` in `Knots.Conway_en`): the PD code does not encode
signs, the unsigned matrix treats negative crossings as positive. The
classical shape is restored only by the signed variant; the determinant
survives (next theorem). -/
theorem alexander_figureEightPlanar_unsigned :
    alexanderPolynomialAux figureEightPlanarDiagram
      = Polynomial.X ^ 3 - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X := by
  simp only [alexanderPolynomialAux, figureEightPlanarDiagram]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-- **The determinant survives the unsigned version**: the unsigned value at
`t = −1` is `−5`, hence `|P(−1)| = 5 = det(4_1)` — losing the polynomial
shape (negative crossings treated as positive) does not destroy the value at
`−1`, a fact already established on the DT code
(`alexander_figureEight_eval_neg_one` in `Knots.Conway_en`). -/
theorem alexander_figureEightPlanar_unsigned_eval_neg_one :
    (alexanderPolynomialAux figureEightPlanarDiagram).eval (-1) = -5 := by
  rw [alexander_figureEightPlanar_unsigned]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_X_pow]
  norm_num

/-! ## 4. Non-tricolorability

The determinant 5 is not divisible by 3: Fox 3-colorability is ruled out
(for a tricolorable knot, det is divisible by 3). Proof by finite enumeration
(kernel `decide`) over the coloring space `Fin 8 → TriColor` (3^8 = 6561),
like the non-planar twin `figureEight_not_tricolorable` in
`Knots.Invariant_en`; the recursion depth limit is lifted at the command
level, for the same reasons documented there. -/

set_option maxRecDepth 100000 in
/-- **The planar figure-eight code is not tricolorable** (Fox 1962). -/
theorem figureEightPlanarDiagram_not_tricolorable :
    ¬ IsTricolorable figureEightPlanarDiagram := by
  decide

/-! ## 5. Crossing count of the diagram (PROVISIONAL definition) -/

/-- The planar code carries exactly 4 crossings (count of the designated
diagram). -/
theorem figureEightPlanarDiagram_numCrossings :
    figureEightPlanarDiagram.numCrossings = 4 := by
  decide

/-- Figure-eight knot carried by the KnotAtlas planar code. -/
def figureEightPlanar : Knot where
  diagram := figureEightPlanarDiagram

/-- The knot `figureEightPlanar` is well-formed (already established on the
diagram by `figureEightPlanarDiagram_wf` in `Knots.Jones_en`). -/
theorem figureEightPlanar_wf : figureEightPlanar.diagram.wf = true :=
  figureEightPlanarDiagram_wf

/-- **Crossing number under the PROVISIONAL Phase 3 definition.**

LIMITATION — this theorem does NOT prove that the topological minimum of
the figure-eight knot is 4. `Knot.crossingNumber` (defined in
`Knots.Basic_en`) is the PROVISIONAL Phase 3 definition: the crossing count
of the designated diagram, which is an UPPER bound on the true topological
minimum. Establishing that the minimum is exactly 4 would require showing
that no equivalent diagram with ≤ 3 crossings exists — the classification
of knots with ≤ 3 crossings, out of reach for this lake. The theorem only
establishes that the designated diagram of `figureEightPlanar` counts 4
crossings, a value that coincides with the expected classical minimum of
4_1 without that coincidence being proven here. -/
theorem figureEightPlanar_crossingNumber_provisional :
    Knot.crossingNumber figureEightPlanar = 4 := by
  show figureEightPlanar.crossingNumberOfDiagram = 4
  unfold Knot.crossingNumberOfDiagram Knot.diagram figureEightPlanar figureEightPlanarDiagram
  decide

end Knots_en

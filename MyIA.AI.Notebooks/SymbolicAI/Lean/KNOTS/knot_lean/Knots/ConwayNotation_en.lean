/-
  Knots.ConwayNotation — Conway's notation for knots
  =================================================

  English mirror of `ConwayNotation.lean` (FR canonical, Pattern A:
  body byte-identical, docstrings translated). Convention EPIC #4980
  (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n).

  Phase 3 of EPIC #2874: the LANGUAGE that generates rational knots.
  `Knots/Conway.lean` carries the Alexander/Conway polynomial and
  `Knots/ConwayPD.lean` the explicit PD diagram of the Conway knot 11n34 —
  neither is Conway's notation. This module introduces the notation: a
  list of integers `[a₁, a₂, …]` (a tangle fraction), even-indexed aᵢ
  counting vertical twists stacked on top, odd-indexed ones horizontal
  twists added on the right flank, then the numerator closure (the two top
  strands joined by an arc, likewise the two bottom ones).

  Method (that of `Knots/ConwayPD.lean`): the construction is validated by
  a Python probe faithful to this lake's definitions — `arcPartition`,
  `alexanderEntry`, the designated minor — on unknot/3₁/4₁/5₁ before the
  Lean port. The probe reproduces the proved designated values of the
  trefoil (t² − t + 1, `alexander_trefoil`) and of the Conway knot 11n34
  (−t⁶, `conway_trivial_alexander`).

  What link 1 proves:

  - the fraction `[2, 2]` yields a well-formed four-crossing diagram whose
    designated polynomial is t³ − 2t² + 2t — the EXACT value of the
    figure-eight knot `figureEightDiagram` (`alexander_figureEight`):
    the notation denotes 4₁ (`conway_notation_22_alexander_figureEight`);
  - `[1]` and `[2]` denote the unknot (designated values 1 and t, a unit);
    so does the empty fraction;
  - `[3]` and `[5]` yield well-formed diagrams whose designated values
    (t², t⁴) are NOT significant: their vertical-chain projection carries
    reflexive edges (closure joining both outgoing strands of one
    crossing), a configuration outside the uniqueness hypotheses of the
    lake's Wirtinger presentation (cf `ArcPartition_en.lean`, "Alexander
    rows sum to zero"). The values are stated as such, with this
    diagnosis — the classical designation of the trefoil awaits a spiral
    construction (rest of the Phase 3 programme).

  What link 2 proves (the spiral construction, §5):

  - the closed 2-strand braid with `n` half-twists read as a spiral
    (annular drawing: crossing `i` carrying the edges `(2i−1, 2i−1+n, 2i,
    2i+n)` modulo `2n`) yields, for `n = 3`, EXACTLY the lake's
    `trefoilDiagram` — the spiral reading of `[3]` denotes 3₁ (designated
    value `t² − t + 1`, that of `alexander_trefoil`);
  - for `n = 5`, the same reading denotes 5₁ (designated value
    `t⁴ − t³ + t² − t + 1`, determinant |Δ(−1)| = 5);
  - no crossing of the spiral carries a reflexive edge: the defect
    diagnosed above on the vertical chains is resolved by the annular
    embedding.

  Sign convention: the lake's PD code does not encode crossing chirality
  (docstring of `alexanderEntry`); only |aᵢ| is read, and the mirror of a
  notation shares all its designated values.

  Epic #2874, Phase 3 "Conway notation for knots". FR sibling:
  `Knots/ConwayNotation.lean`.
-/

import Knots.Basic_en
import Knots.Conway_en

open Knots_en

namespace Knots_en

/-! ## 1. Algebraic tangles — a four-port state

A four-strand tangle is represented by its partial PD crossings and the
labels of its four ports NW, NE, SW, SE. The null tangle (two vertical
strands) shares one label between both ports of a strand.
-/

/-- State of an algebraic tangle: partial crossings, labels of the four
ports, next fresh label. -/
structure TangleSt where
  crossings : List PDCrossing
  nw : Nat
  ne : Nat
  sw : Nat
  se : Nat
  next : Nat

/-- The null tangle: two vertical strands, the left one carrying label 1
(SW and NW), the right one label 2 (SE and NE). -/
def TangleSt.zero : TangleSt := ⟨[], 1, 2, 1, 2, 3⟩

/-- Replaces label `b` by `a` in a crossing. -/
def relabelCross (a b : Nat) (c : PDCrossing) : PDCrossing :=
  ⟨if c.e1 = b then a else c.e1, if c.e2 = b then a else c.e2,
   if c.e3 = b then a else c.e3, if c.e4 = b then a else c.e4⟩

/-- Fusion of two port labels: `b` becomes `a` everywhere. -/
def TangleSt.relabel (t : TangleSt) (a b : Nat) : TangleSt :=
  { t with crossings := t.crossings.map (relabelCross a b) }

/-- A vertical twist on top: crosses the two upper strands (the strand
coming from the left passes under) and swaps them — the strand entering on
the left exits on the right. -/
def TangleSt.vTwist (t : TangleSt) : TangleSt :=
  { t with
    crossings := t.crossings ++ [⟨t.nw, t.ne, t.next + 1, t.next⟩]
    nw := t.next
    ne := t.next + 1
    next := t.next + 2 }

/-- A horizontal twist on the right flank: crosses the two right strands
(the strand coming from below passes under) and swaps them — the strand
entering on top exits below. -/
def TangleSt.hTwist (t : TangleSt) : TangleSt :=
  { t with
    crossings := t.crossings ++ [⟨t.se, t.ne, t.next, t.next + 1⟩]
    ne := t.next
    se := t.next + 1
    next := t.next + 2 }

/-- Stacks `k` vertical twists. -/
def TangleSt.twistsV : Nat → TangleSt → TangleSt
  | 0, t => t
  | k + 1, t => t.twistsV k |>.vTwist

/-- Stacks `k` horizontal twists. -/
def TangleSt.twistsH : Nat → TangleSt → TangleSt
  | 0, t => t
  | k + 1, t => t.twistsH k |>.hTwist

/-! ## 2. The Conway fraction

The notation `[a₁, a₂, …]`: zero-indexed even aᵢ count vertical twists on
top, odd-indexed ones horizontal twists on the right flank. The numerator
closure joins the two top strands (NW ~ NE) then the bottom ones (SW ~ SE).
The sign of the aᵢ is not read: the lake's PD does not encode chirality,
a notation's mirror shares its designated values.
-/

/-- Construction of a notation's tangle, alternating vertical/horizontal. -/
def conwayTangleAux : Nat → List ℤ → TangleSt → TangleSt
  | _, [], t => t
  | i, n :: rest, t =>
      let k := n.natAbs
      conwayTangleAux (i + 1) rest
        (if i % 2 = 0 then t.twistsV k else t.twistsH k)

/-- The algebraic tangle denoted by a Conway notation. -/
def conwayTangle (ns : List ℤ) : TangleSt :=
  conwayTangleAux 0 ns TangleSt.zero

/-- Numerator closure: top arc (NW ~ NE) then bottom arc (SW ~ SE). -/
def TangleSt.numClosure (t : TangleSt) : TangleSt :=
  let t1 := t.relabel t.nw t.ne
  t1.relabel t1.sw t1.se

/-- Renumbers a label: keeps the table of seen labels and the counter. -/
def renumberStep (x : Nat) (m : List (Nat × Nat)) (k : Nat) :
    Nat × (List (Nat × Nat)) × Nat :=
  match m.lookup x with
  | some y => (y, m, k)
  | none => (k + 1, (x, k + 1) :: m, k + 1)

/-- Renumbers the crossings by first appearance of the label. -/
def renumberCrossingsAux : List PDCrossing → List (Nat × Nat) → Nat →
    List PDCrossing × List (Nat × Nat) × Nat
  | [], m, k => ([], m, k)
  | c :: cs, m, k =>
      let e1 := renumberStep c.e1 m k
      let e2 := renumberStep c.e2 e1.2.1 e1.2.2
      let e3 := renumberStep c.e3 e2.2.1 e2.2.2
      let e4 := renumberStep c.e4 e3.2.1 e3.2.2
      let rest := renumberCrossingsAux cs e4.2.1 e4.2.2
      (⟨e1.1, e2.1, e3.1, e4.1⟩ :: rest.1, rest.2.1, rest.2.2)

/-- The diagram denoted by a Conway notation: the fraction's tangle,
numerator-closed, renumbered to contiguous labels `1..numEdges`. -/
def conwayKnotOf (ns : List ℤ) : KnotDiagram :=
  let t := (conwayTangle ns).numClosure
  let r := renumberCrossingsAux t.crossings [] 0
  ⟨r.1, r.2.2⟩

/-- Named notations: the link's examples. -/
def unknotNotation : List ℤ := []
def oneTwistNotation : List ℤ := [1]
def twoTwistNotation : List ℤ := [2]
def trefoilNotation : List ℤ := [3]
def figureEightNotation : List ℤ := [2, 2]
def cinquefoilNotation : List ℤ := [5]

/-! ## 3. Well-formedness

Each example yields a well-formed diagram: every label of `[1, numEdges]`
exactly twice. Decidable on these instances.
-/

theorem conway_wf_empty : (conwayKnotOf unknotNotation).wf = true := by
  decide

theorem conway_wf_one : (conwayKnotOf oneTwistNotation).wf = true := by
  decide

theorem conway_wf_two : (conwayKnotOf twoTwistNotation).wf = true := by
  decide

theorem conway_wf_three : (conwayKnotOf trefoilNotation).wf = true := by
  decide

theorem conway_wf_five : (conwayKnotOf cinquefoilNotation).wf = true := by
  decide

theorem conway_wf_22 : (conwayKnotOf figureEightNotation).wf = true := by
  decide

/-! ## 4. The designated Alexander polynomial of the examples

The proofs follow the `alexander_trefoil` pattern: the arc partition by
`decide`, then the minor unfolds and `ring`. The values are those of the
faithful Python probe (module header).
-/

/-- Determinant of a generic 4×4 matrix (same spirit as `det_two_aux` /
`det_three_aux` of `Knots/Conway.lean`: Laplace expansion along the first
column, the 3×3 minors handled by `det_three_aux`). -/
theorem conway_det_four_aux (A : Matrix (Fin 4) (Fin 4) (Polynomial ℤ)) :
    A.det =
      A 0 0 * (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2)
             - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
             + A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))
      - A 1 0 * (A 0 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2)
              - A 0 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
              + A 0 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))
      + A 2 0 * (A 0 1 * (A 1 2 * A 3 3 - A 1 3 * A 3 2)
              - A 0 2 * (A 1 1 * A 3 3 - A 1 3 * A 3 1)
              + A 0 3 * (A 1 1 * A 3 2 - A 1 2 * A 3 1))
      - A 3 0 * (A 0 1 * (A 1 2 * A 2 3 - A 1 3 * A 2 2)
              - A 0 2 * (A 1 1 * A 2 3 - A 1 3 * A 2 1)
              + A 0 3 * (A 1 1 * A 2 2 - A 1 2 * A 2 1)) := by
  rw [Matrix.det_succ_column_zero]
  simp (config := { decide := true }) [Fin.sum_univ_succ]
  simp (config := { decide := true }) [det_three_aux, Matrix.submatrix_apply, Fin.succAbove]
  ring

/-- The empty fraction denotes the unknot: crossingless diagram, empty
determinant. The diagram is first literalised by `decide` (`conwayKnotOf`
is a recursive function `simp only` does not compute -- same role as
`simp only [trefoilDiagram]` in `alexander_trefoil`). -/
theorem conway_unknot_alexander :
    alexanderPolynomialAux (conwayKnotOf unknotNotation) = 1 := by
  have hc : conwayKnotOf unknotNotation = ⟨[], 0⟩ := by
    decide
  simp only [alexanderPolynomialAux, hc]

/-- One closed twist is an R1 kink: the unknot, designated value 1 (empty
minor). -/
theorem conway_one_alexander :
    alexanderPolynomialAux (conwayKnotOf oneTwistNotation) = 1 := by
  have hc : conwayKnotOf oneTwistNotation = ⟨[⟨1, 1, 2, 2⟩], 2⟩ := by
    decide
  have hp : arcPartition (conwayKnotOf oneTwistNotation) = [[1, 2]] := by
    decide
  simp only [alexanderPolynomialAux, hp, hc]
  simp (config := { decide := true })

/-- Two closed twists: two chained R1 kinks, the unknot — designated value
t, a unit (1×1 minor). -/
theorem conway_two_alexander :
    alexanderPolynomialAux (conwayKnotOf twoTwistNotation) = Polynomial.X := by
  have hc : conwayKnotOf twoTwistNotation =
      ⟨[⟨1, 1, 2, 3⟩, ⟨3, 2, 4, 4⟩], 4⟩ := by
    decide
  have hp : arcPartition (conwayKnotOf twoTwistNotation) = [[1, 3], [2, 4]] := by
    decide
  simp only [alexanderPolynomialAux, hp, hc]
  simp (config := { decide := true }) [alexanderEntry]

/-- The fraction `[2, 2]` denotes the figure-eight knot: its diagram (four
crossings, eight edges, no reflexive one — the horizontal twists divert
the closure ports) carries the EXACT designated value of
`figureEightDiagram`, t³ − 2t² + 2t (the chirality artefact documented in
`Knots/Conway.lean` §"Divergence of the 4-crossing class", #14962: the
determinant |Δ(−1)| = 5 = det(4₁) is faithfully reproduced). -/
theorem conway_notation_22_alexander :
    alexanderPolynomialAux (conwayKnotOf figureEightNotation) =
      Polynomial.X ^ 3 - (2 : Polynomial ℤ) * Polynomial.X ^ 2
        + 2 * Polynomial.X := by
  have hc : conwayKnotOf figureEightNotation =
      ⟨[⟨1, 2, 3, 4⟩, ⟨4, 3, 5, 6⟩, ⟨2, 5, 7, 8⟩, ⟨8, 7, 6, 1⟩], 8⟩ := by
    decide
  have hp : arcPartition (conwayKnotOf figureEightNotation) =
      [[2, 4], [3, 6], [5, 8], [1, 7]] := by
    decide
  simp only [alexanderPolynomialAux, hp, hc]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-- Corollary: the designated value of `[2, 2]` is exactly that of the
lake's figure-eight knot — Conway's notation denotes 4₁. -/
theorem conway_notation_22_alexander_figureEight :
    alexanderPolynomialAux (conwayKnotOf figureEightNotation) =
      alexanderPolynomial figureEight := by
  rw [conway_notation_22_alexander, alexander_figureEight]

/-- The fraction `[3]` (the trefoil of Conway's tables) here yields a
vertical-chain projection: the closure arcs join both outgoing strands of
one crossing (reflexive edges), a configuration outside the uniqueness
hypotheses of the Wirtinger presentation — the designated value t² is NOT
significant (it is not a unit times t² − t + 1; the computed minors are
±1 and t²). The underlying knot is indeed 3₁ (classical fact: the
numerator closure of the three-twist tangle); its classical designation
requires a spiral construction, next step of the Phase 3 programme —
delivered in link 2 (§5: `spiral_three_designates_trefoil`). -/
theorem conway_three_designated :
    alexanderPolynomialAux (conwayKnotOf trefoilNotation) = Polynomial.X ^ 2 := by
  have hc : conwayKnotOf trefoilNotation =
      ⟨[⟨1, 1, 2, 3⟩, ⟨3, 2, 4, 5⟩, ⟨5, 4, 6, 6⟩], 6⟩ := by
    decide
  have hp : arcPartition (conwayKnotOf trefoilNotation) =
      [[1, 3], [2, 5], [4, 6]] := by
    decide
  simp only [alexanderPolynomialAux, hp, hc]
  simp (config := { decide := true })
  rw [det_two_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-- Same diagnosis for `[5]` (5₁ of the tables): pure vertical chain,
reflexive edges, designated value t⁴ not significant — resolved in
link 2 (§5: `spiral_five_alexander`). -/
theorem conway_five_designated :
    alexanderPolynomialAux (conwayKnotOf cinquefoilNotation) = Polynomial.X ^ 4 := by
  have hc : conwayKnotOf cinquefoilNotation =
      ⟨[⟨1, 1, 2, 3⟩, ⟨3, 2, 4, 5⟩, ⟨5, 4, 6, 7⟩, ⟨7, 6, 8, 9⟩, ⟨9, 8, 10, 10⟩], 10⟩ := by
    decide
  have hp : arcPartition (conwayKnotOf cinquefoilNotation) =
      [[1, 3], [2, 5], [4, 7], [6, 9], [8, 10]] := by
    decide
  simp only [alexanderPolynomialAux, hp, hc]
  simp (config := { decide := true })
  rw [conway_det_four_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring


/-! ## 5. The spiral construction (link 2)

The defect of link 1 — the numerator closure as a vertical chain joins
both outgoing strands of one crossing (reflexive edges) — is not a defect
of the LANGUAGE but of the DRAWING: the same fraction `[n]` is drawn by
winding the closed 2-strand braid around a cylinder, each crossing `i`
carrying the four edges `(2i−1, 2i−1+n, 2i, 2i+n)` read modulo `2n`. For
`n` odd (`n ≥ 3`), the numerator closure of the tangle `[n]` is the torus
knot `T(2, n)` (classical fact): `[3]` denotes 3₁, `[5]` denotes 5₁. The
designated values below are those of the module's Python probe (header),
validated before the port.
-/

/-- Spiral label: `k` read modulo `2n`, in `1..2n`. -/
def spiralLabel (n k : Nat) : Nat := (k - 1) % (2 * n) + 1

/-- Crossing `i` (1-indexed) of the spiral with `n` half-twists: the two
incoming edges `2i−1` and `2i`, the two outgoing ones shifted by `n` (half
a cylinder turn further along the coil). -/
def spiralCross (n i : Nat) : PDCrossing :=
  ⟨spiralLabel n (2 * i - 1), spiralLabel n (2 * i - 1 + n),
   spiralLabel n (2 * i), spiralLabel n (2 * i + n)⟩

/-- The closed 2-strand braid with `n` half-twists, wound as a spiral: the
annular drawing of the fraction `[n]` (for `n` odd ≥ 3, the torus knot
`T(2, n)`), without reflexive edge. -/
def spiralDiagram (n : Nat) : KnotDiagram :=
  ⟨(List.range n).map (fun i => spiralCross n (i + 1)), 2 * n⟩

/-! ### Well-formedness

Each label of `1..2n` appears exactly twice, in two distinct crossings —
in particular the four labels of a crossing are pairwise distinct: the
Wirtinger defect of link 1 vanishes.
-/

theorem spiral_wf_three : (spiralDiagram 3).wf = true := by
  decide

theorem spiral_wf_five : (spiralDiagram 5).wf = true := by
  decide

/-- No reflexive edge in the spiral `[3]`: the four labels of each
crossing are pairwise distinct. -/
theorem spiral_noReflect_three :
    (spiralDiagram 3).crossings.all (fun c =>
      c.e1 ≠ c.e2 ∧ c.e1 ≠ c.e3 ∧ c.e1 ≠ c.e4 ∧
      c.e2 ≠ c.e3 ∧ c.e2 ≠ c.e4 ∧ c.e3 ≠ c.e4) = true := by
  decide

/-- Same absence of reflexive edges for the spiral `[5]`. -/
theorem spiral_noReflect_five :
    (spiralDiagram 5).crossings.all (fun c =>
      c.e1 ≠ c.e2 ∧ c.e1 ≠ c.e3 ∧ c.e1 ≠ c.e4 ∧
      c.e2 ≠ c.e3 ∧ c.e2 ≠ c.e4 ∧ c.e3 ≠ c.e4) = true := by
  decide

/-! ### The designated values of the spirals

`[3]` denotes the trefoil: the three-half-twist spiral literalises
EXACTLY the lake's reference diagram (`trefoilDiagram`,
`Knots/Basic_en.lean`) — the designation follows by `alexander_trefoil`.
`[5]` denotes 5₁: designated value `t⁴ − t³ + t² − t + 1`, determinant
|Δ(−1)| = 5.
-/

/-- The spiral `[3]` IS the lake's trefoil diagram, edge for edge: the
annular reading of the fraction `[3]` yields the reference PD
`trefoilDiagram`. -/
theorem spiral_three_eq_trefoilDiagram :
    spiralDiagram 3 = trefoilDiagram := by
  decide

/-- The designated value of the spiral `[3]`: `t² − t + 1`, computed in
place (the `alexander_trefoil` pattern — literalisation, arc partition,
2×2 minor). -/
theorem spiral_three_alexander :
    alexanderPolynomialAux (spiralDiagram 3) =
      Polynomial.X ^ 2 - Polynomial.X + 1 := by
  have hc : spiralDiagram 3 =
      ⟨[⟨1, 4, 2, 5⟩, ⟨3, 6, 4, 1⟩, ⟨5, 2, 6, 3⟩], 6⟩ := by
    decide
  simp only [alexanderPolynomialAux, hc]
  simp (config := { decide := true })
  rw [det_two_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-- Designation corollary: the spiral `[3]` carries exactly the Alexander
polynomial of the lake's trefoil — the notation denotes 3₁, and link 1's
reflexive diagnosis is resolved by the annular embedding. -/
theorem spiral_three_designates_trefoil :
    alexanderPolynomialAux (spiralDiagram 3) = alexanderPolynomial trefoil := by
  rw [spiral_three_alexander, alexander_trefoil]

/-- The designated value of the spiral `[5]`: `t⁴ − t³ + t² − t + 1`, the
Alexander polynomial of 5₁ (determinant |Δ(−1)| = 5). The 4×4 minor is
unfolded by `conway_det_four_aux`. -/
theorem spiral_five_alexander :
    alexanderPolynomialAux (spiralDiagram 5) =
      Polynomial.X ^ 4 - Polynomial.X ^ 3 + Polynomial.X ^ 2
        - Polynomial.X + 1 := by
  have hc : spiralDiagram 5 =
      ⟨[⟨1, 6, 2, 7⟩, ⟨3, 8, 4, 9⟩, ⟨5, 10, 6, 1⟩, ⟨7, 2, 8, 3⟩,
        ⟨9, 4, 10, 5⟩], 10⟩ := by
    decide
  simp only [alexanderPolynomialAux, hc]
  simp (config := { decide := true })
  rw [conway_det_four_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

end Knots_en

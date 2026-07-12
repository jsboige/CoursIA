/-
  Knots.Basic — Combinatorial foundations of knot theory
  =====================================================

  Scaffolding for knot theory in Lean 4, inspired by:
  - shua/leanknot (https://github.com/shua/leanknot, Lean 4 branch)
  - Prathamesh (2015), Formalising Knot Theory in Isabelle/HOL

  Convention: namespace `Knots`, sorry commentés avec références.
  Epic #2874, Phase 1.

  Mathlib prerequisites needed:
  - Combinatorial representations of planar diagrams (PD-codes)
  - Gauss codes / Dowker-Thistlethwaite notation
  - Basic graph theory for crossing graphs
-/

namespace Knots

/-! ## 1. Crossing and CrossingType

A crossing in a knot diagram has two strands: one goes over, one goes under.
The sign distinguishes positive (right-handed) from negative (left-handed) crossings.
-/

inductive CrossingType where
  | positive : CrossingType  -- over-crossing from left
  | negative : CrossingType  -- over-crossing from right
  deriving BEq, DecidableEq, Repr

instance : Repr CrossingType := ⟨fun ct _ =>
  match ct with
  | .positive => "+"
  | .negative => "-"⟩

/-! ## 2. Crossing

A crossing is identified by its index in a diagram and has a type.
-/

structure Crossing where
  index : Nat
  crossingType : CrossingType
  deriving BEq, DecidableEq, Repr

/-! ## 3. Strand segment

Between two crossings (or from a crossing back to itself), a strand segment
connects positions. We label positions as "incoming" or "outgoing" for each
crossing arm.
-/

inductive Arm where
  | over_in : Arm
  | over_out : Arm
  | under_in : Arm
  | under_out : Arm
  deriving BEq, DecidableEq, Repr

/-! ## 4. Planar Diagram (PD) Code

A crossing is encoded by four edge labels meeting at that crossing,
read counterclockwise starting from the incoming under-strand.

Reference: https://katlas.org/wiki/Planar_Diagrams
-/

structure PDCrossing where
  -- Four edge labels, counterclockwise from incoming under-strand
  e1 : Nat  -- incoming under
  e2 : Nat  -- incoming over
  e3 : Nat  -- outgoing under
  e4 : Nat  -- outgoing over
  deriving BEq, Repr

/-- A knot diagram is a list of PD-crossings with a crossing count. -/
structure KnotDiagram where
  crossings : List PDCrossing
  numEdges : Nat
  -- TODO Phase 2: well-formedness predicate.
  -- Each edge label 0..numEdges-1 appears exactly twice across all crossings.
  -- Reference: Doll & Hoste (1991), A tabulation of oriented links.
  -- Placeholder `True` until the predicate is formalised; do NOT read as "well-formed".
  hwell : True
  deriving Repr

/-! ## 5. Knot

A knot is an equivalence class of knot diagrams under Reidemeister moves
and planar isotopy. For now, we represent it as a wrapper around a diagram,
with equivalence defined but not yet connected to Reidemeister moves.
-/

structure Knot where
  diagram : KnotDiagram
  deriving Repr

/-! ## 6. Link

A link extends a knot to multiple components. Represented as a PD-code
with multiple closed curves.
-/

structure Link where
  diagram : KnotDiagram
  numComponents : Nat
  -- At least 1 component (knot = link with 1 component)
  hpos : numComponents ≥ 1
  deriving Repr

/-- A knot is a link with exactly one component. -/
def Knot.toLink (k : Knot) : Link where
  diagram := k.diagram
  numComponents := 1
  hpos := by omega

/-! ## 7. Named knots

The simplest knot: the unknot (no crossings).
-/

def unknotDiagram : KnotDiagram where
  crossings := []
  numEdges := 1
  hwell := by trivial

def unknot : Knot where
  diagram := unknotDiagram

/- The trefoil knot (3_1), the simplest non-trivial knot.

Crossing number 3, three positive crossings (right-hand trefoil).
PD-code from KnotInfo: [[1,4,2,5],[3,6,4,1],[5,2,6,3]]
-/
def trefoilDiagram : KnotDiagram where
  crossings := [
    ⟨1, 4, 2, 5⟩,  -- crossing 1
    ⟨3, 6, 4, 1⟩,  -- crossing 2
    ⟨5, 2, 6, 3⟩   -- crossing 3
  ]
  numEdges := 6
  hwell := by trivial  -- TODO: proper well-formedness check

def trefoil : Knot where
  diagram := trefoilDiagram

/- The figure-eight knot (4_1), the simplest knot with crossing number 4.

PD-code from KnotInfo: [[1,5,2,4],[3,8,4,2],[5,1,6,7],[7,3,8,6]]
-/
def figureEightDiagram : KnotDiagram where
  crossings := [
    ⟨1, 5, 2, 4⟩,
    ⟨3, 8, 4, 2⟩,
    ⟨5, 1, 6, 7⟩,
    ⟨7, 3, 8, 6⟩
  ]
  numEdges := 8
  hwell := by trivial  -- TODO: proper well-formedness check

def figureEight : Knot where
  diagram := figureEightDiagram

/-! ## 8. Mirror image

Mirror a knot by reversing all crossing signs (swap over/under).
-/

def mirrorCrossing (c : PDCrossing) : PDCrossing where
  e1 := c.e1
  e2 := c.e4  -- swap over and under
  e3 := c.e3
  e4 := c.e2

def Knot.mirror (k : Knot) : Knot where
  diagram := {
    crossings := k.diagram.crossings.map mirrorCrossing
    numEdges := k.diagram.numEdges
    hwell := k.diagram.hwell  -- mirror preserves well-formedness
  }

/-! ## 9. Crossing number (minimal crossings)

The crossing number is the minimum number of crossings over all diagrams
representing the same knot. This requires equivalence, which we don't have yet.
-/

def Knot.crossingNumberOfDiagram (k : Knot) : Nat :=
  k.diagram.crossings.length

/-- Crossing number.

**Phase 3 definition (provisional upper bound).** The true crossing number
is the *minimum* number of crossings over all diagrams equivalent to `k`
under Reidemeister moves. Computing that minimum requires:
  - a fully concrete Reidemeister equivalence (surgery on PD-codes), and
  - a minimisation (finset min over the quotient of diagrams).

Neither is available yet (Reidemeister moves are still abstract, cf.
`Reidemeister.lean`). As a *provisional, conservative* definition we take the
crossing count of the knot's current diagram. This is an **upper bound** on the
true crossing number (Reidemeister I can only add crossings, never reduce below
the minimal diagram), so it is sound to use as an upper estimate.

For the named knots whose standard diagrams are already minimal (unknot = 0,
trefoil = 3, figure-eight = 4) this coincides with the true crossing number.
The `trefoil_crossing_number` theorem in `Invariant.lean` relies on this
provisional definition.

TODO Phase 4+: replace by the genuine minimum once concrete Reidemeister
equivalence + finset minimisation are in place.
-/
def Knot.crossingNumber (k : Knot) : Nat :=
  k.crossingNumberOfDiagram

/-! ## 10. Connectivity / adjacency from PD-code

Extract which edges connect which crossings.
-/

/-- Get all edges used in a diagram. -/
def KnotDiagram.edges (d : KnotDiagram) : List Nat :=
  d.crossings.flatMap fun c => [c.e1, c.e2, c.e3, c.e4]

/-- Number of crossings in a diagram. -/
def KnotDiagram.numCrossings (d : KnotDiagram) : Nat :=
  d.crossings.length

/-! ## 11. Well-formedness predicate (Phase 5)

A PD-code is well-formed when (a) every edge label is in `[1, numEdges]`, and
(b) every label that occurs occurs exactly twice — each arc has two endpoints,
one at each crossing it meets (Doll & Hoste, 1991). A degenerate diagram with
no crossings has an empty edge list, so both conditions hold vacuously.

This is a *Bool-valued standalone predicate* (not a `KnotDiagram` field),
modelled on `MacroCell.wf` in `conway_lean` (HashlifeCorrectness.lean). It is
threaded as a hypothesis `(hwf : d.wf = true)` on the re-modeled Reidemeister
moves (see `Reidemeister.lean`), which is what excludes the malformed witnesses
that refuted `tricolorable_invariant` under the Phase 3 symmetric-existential
model (see the diagnostic on `tricolorable_invariant` in `Invariant.lean`).
-/

/-- Well-formedness for a PD-code (Bool-valued, mirrored on `MacroCell.wf`).

A genuine PD-code satisfies the **parity condition**: every edge label in
`[1, numEdges]` appears exactly twice among the crossing endpoints — each arc
has two endpoints, one at each crossing it meets (so `2 * numEdges = 4 *
numCrossings`, i.e. `numEdges = 2 * numCrossings` for non-degenerate diagrams).

A degenerate diagram with no crossings has no edge endpoints; its edge list is
empty, and the parity condition holds vacuously for any `numEdges ≤ 1` (the
unknot is represented with one arc, `numEdges := 1`).

The predicate is threaded as `(hwf : d.wf = true)` on the re-modeled
Reidemeister moves (`Reidemeister.lean`), excluding the malformed witnesses that
refuted `tricolorable_invariant` under the Phase 3 symmetric-existential model
(the witness `⟨7,8,9,10⟩` has labels out of `[1, numEdges]`; a dangling-edge
diagram has a label in `[1, numEdges]` that never occurs). See the diagnostic on
`tricolorable_invariant` in `Invariant.lean`. -/
def KnotDiagram.wf (d : KnotDiagram) : Bool :=
  if d.crossings = [] then
    decide (d.numEdges ≤ 1)
  else
    -- (a) every label occurring in a crossing is in [1, numEdges]
    d.edges.all (fun l => decide (1 ≤ l ∧ l ≤ d.numEdges)) &&
    -- (b) every label in [1, numEdges] occurs exactly twice (parity)
    (List.range d.numEdges).all (fun i => decide (d.edges.count (i + 1) = 2))

theorem unknot_wf : unknotDiagram.wf = true := by
  -- 0 crossings → degenerate branch: numEdges = 1 ≤ 1.
  decide

theorem trefoil_wf : trefoilDiagram.wf = true := by
  -- 3 crossings, labels {1,..,6} each appearing exactly twice.
  decide

theorem figureEight_wf : figureEightDiagram.wf = true := by
  -- 4 crossings, labels {1,..,8} each appearing exactly twice.
  decide

end Knots

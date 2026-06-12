/-
  Knots.Invariant — Knot invariants (3-colorability, crossing number)
  ====================================================================

  Knot invariants distinguish knots. This file scaffolds:
  1. Tricolorability (Fox 1962) — the most accessible invariant
  2. Crossing number bounds
  3. Unknotting number (definition only, sorry)

  Epic #2874, Phase 1–2.

  Mathlib prerequisites needed:
  - Finite colorings of graphs (Fintype, Fin n coloring)
  - Minimization over equivalence classes
-/

import Knots.Basic
import Knots.Reidemeister

namespace Knots

/-! ## 1. Tricolorability (Fox 1962)

A knot diagram is tricolorable if each strand can be colored with one
of 3 colors such that:
  (a) At each crossing, either all three strands have the same color,
      or all three have different colors.
  (b) At least two colors are used.

This is the simplest non-trivial knot invariant.

Reference: Fox (1962), A quick trip through knot theory.
-/

/-- Three colors for tricolorability. -/
inductive TriColor where
  | red : TriColor
  | blue : TriColor
  | green : TriColor
  deriving BEq, DecidableEq, Repr, Fintype

instance : Fintype TriColor := inferInstance

/-- A tricoloring assigns a color to each edge in a knot diagram. -/
def TriColoring (d : KnotDiagram) := Fin d.numEdges → TriColor

/-- Check the tricolorability condition at a single crossing.

At a crossing with strands colored c_in, c_over, c_out:
either all equal, or all distinct.
-/
def triColorConditionAt (coloring : Fin d.numEdges → TriColor) (c : PDCrossing) : Prop :=
  let c1 := sorry  -- TODO: edge index for incoming under-strand
  let c2 := sorry  -- TODO: edge index for over-strand
  let c3 := sorry  -- TODO: edge index for outgoing under-strand
  -- All same OR all different
  (coloring c1 = coloring c2 ∧ coloring c2 = coloring c3) ∨
  (coloring c1 ≠ coloring c2 ∧ coloring c2 ≠ coloring c3 ∧ coloring c1 ≠ coloring c3)
  -- TODO: proper edge-index extraction from PDCrossing

/-- A valid tricoloring: satisfies the condition at every crossing,
and uses at least 2 colors. -/
def IsTriColoring (d : KnotDiagram) (coloring : TriColoring d) : Prop :=
  (∀ c ∈ d.crossings, triColorConditionAt (↑coloring) c) ∧
  (∃ i j, coloring i ≠ coloring j)
  -- TODO: proper well-typed version once edge indexing is fixed

/-- A diagram is tricolorable if a valid tricoloring exists. -/
def IsTricolorable (d : KnotDiagram) : Prop :=
  ∃ coloring : TriColoring d, IsTriColoring d coloring

/-- A knot is tricolorable if any of its diagrams is. -/
def Knot.isTricolorable (k : Knot) : Prop :=
  IsTricolorable k.diagram

/-! ## 2. Tricolorability is an invariant

Tricolorability is preserved by all three Reidemeister moves.
This is the key theorem that makes it a knot invariant.

**Phase 2 target**: prove this!
-/

theorem tricolorable_invariant :
    ∀ (d₁ d₂ : KnotDiagram),
      ReidemeisterEquiv d₁ d₂ →
      IsTricolorable d₁ ↔ IsTricolorable d₂ := by
  exact sorry
  -- Reference: Fox (1962), standard textbook proof
  -- Proof strategy: check each of the 3 Reidemeister moves
  --   R1 (twist): a curl adds one strand, trivially extends coloring
  --   R2 (poke): two parallel strands, either both same color or both different
  --   R3 (slide): casework on the 3 colors involved
  -- Mathlib prerequisites:
  --   1. Fin n → TriColor (function type, exists in Mathlib)
  --   2. Decidable equality on TriColor (derive)
  --   3. Universal/existential quantifiers over finite types
  -- Difficulty: **accessible** — good target for Phase 2

/-! ## 3. The trefoil is tricolorable

The trefoil (3_1) can be colored with 3 colors, each crossing seeing
all three colors. This proves the trefoil is NOT the unknot.
-/

theorem trefoil_tricolorable : Knot.isTricolorable trefoil := by
  exact sorry
  -- Reference: Fox (1962)
  -- Proof: assign red, blue, green cyclically to the 3 strands
  --   Strand 1 → red, Strand 2 → blue, Strand 3 → green
  --   At each crossing: all three colors are different ✓
  --   Uses 3 colors ≥ 2 ✓
  -- Phase 2 target — **most accessible theorem** in the whole project
  -- Mathlib prerequisites: just need proper edge indexing

/-! ## 4. The unknot is NOT tricolorable

The unknot has a diagram with no crossings. Any coloring uses only
one strand, so the "at least 2 colors" condition fails.
-/

theorem unknot_not_tricolorable : ¬ Knot.isTricolorable unknot := by
  exact sorry
  -- Reference: Fox (1962)
  -- Proof: the unknot has a 0-crossing diagram
  --   Only 1 edge → only 1 color → fails "at least 2 colors"
  -- Phase 2 target

/-! ## 5. Corollary: the trefoil is not the unknot

Since tricolorability is an invariant, and the trefoil has it
but the unknot doesn't, they are different knots.
-/

theorem trefoil_not_unknot : ¬ KnotEquiv trefoil unknot := by
  intro h
  have h1 := (tricolorable_invariant unknotDiagram unknotDiagram
    (ReidemeisterEquiv.refl unknotDiagram)).mp unknot_not_tricolorable
  -- If trefoil ≈ unknot, then trefoil tricolorable ↔ unknot tricolorable
  -- But trefoil IS tricolorable and unknot IS NOT → contradiction
  have := (tricolorable_invariant trefoilDiagram unknotDiagram).mp trefoil_tricolorable
  exact sorry  -- TODO: wire up the contradiction properly
  -- Phase 2 target — consequence of the above 3 theorems

/-! ## 6. Crossing number bounds

The crossing number of a diagram gives an upper bound on the
minimal crossing number of the knot.
-/

/-- The trefoil has crossing number exactly 3.

This requires showing both:
  (a) there exists a diagram with 3 crossings (obvious)
  (b) no diagram with fewer crossings represents the trefoil

Part (b) requires the classification of knots by crossing number.
-/
theorem trefoil_crossing_number :
    Knot.crossingNumber trefoil = 3 := by
  exact sorry
  -- Reference: standard knot theory
  -- Proof: the trefoil is the unique knot with crossing number 3
  -- (up to chirality: left vs right trefoil)
  -- Mathlib prerequisites: classification of knots by crossing number
  -- Phase 3 target

/-! ## 7. Unknotting number (definition only)

The unknotting number u(K) is the minimum number of crossing changes
needed to turn K into the unknot. This is a much harder invariant.

Reference: unknotting number is NP-hard to compute in general.
-/

/-- Change a crossing from positive to negative or vice versa. -/
def changeCrossing (c : PDCrossing) : PDCrossing where
  e1 := c.e1
  e2 := c.e4  -- swap over and under at this crossing
  e3 := c.e3
  e4 := c.e2

/-- Unknotting number: minimum crossing changes to reach the unknot. -/
def Knot.unknottingNumber (k : Knot) : Nat := by
  exact sorry
  -- Definition: min {n : ∃ diagram, n crossing changes → unknot diagram}
  -- Reference: standard definition
  -- Mathlib prerequisites:
  --   1. Minimization over equivalence classes
  --   2. Reachability in a graph of diagrams
  -- This definition requires substantial infrastructure
  -- Phase 4+ target

end Knots

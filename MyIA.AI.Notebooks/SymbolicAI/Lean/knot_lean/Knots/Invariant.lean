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
  deriving BEq, DecidableEq, Repr

/-- A tricoloring assigns a color to each edge in a knot diagram. -/
def TriColoring (d : KnotDiagram) := Fin d.numEdges → TriColor

/-- The three local strands of a crossing relevant for tricolorability:
the incoming under-strand (`e1`), the over-strand (`e2`), and the outgoing
under-strand (`e3`). In PD notation these are the three arcs meeting at the
crossing. -/
def PDCrossing.localStrands (c : PDCrossing) : Nat × Nat × Nat :=
  (c.e1, c.e2, c.e3)

/-- Total coloring lookup on a raw `Nat` label, clamped to a valid index.

PD edge labels are 1-indexed in range `[1, numEdges]` for well-formed diagrams.
This total wrapper returns the color at index `(l - 1) mod numEdges` (or `red`
when `numEdges = 0`), so the Fox condition below can be stated without threading
bound proofs through the term. The well-formedness hypothesis
(`1 ≤ l ≤ numEdges`) is recorded separately as part of `triColorConditionAt`,
making the total-vs-partial gap explicit and auditable. -/
def KnotDiagram.colorAtNat (d : KnotDiagram)
    (coloring : Fin d.numEdges → TriColor) (l : Nat) : TriColor :=
  if h : d.numEdges = 0 then TriColor.red
  else coloring ⟨(l - 1) % d.numEdges, Nat.mod_lt _ (by omega)⟩

/-- Check the tricolorability condition at a single crossing.

At a crossing with local strands `e1` (incoming under), `e2` (over), `e3`
(outgoing under): either all three carry the same color, or all three carry
pairwise distinct colors. This is Fox's (1962) condition.

For well-formed crossings (labels in `[1, numEdges]`, the first conjunct),
`colorAtNat` reads the genuine coloring at `e1`, `e2`, `e3`. For malformed
labels the conjunct fails and the crossing is not tricolorable-satisfying —
the condition is sound even before the diagram well-formedness predicate lands.
-/
def triColorConditionAt (d : KnotDiagram) (coloring : Fin d.numEdges → TriColor)
    (c : PDCrossing) : Prop :=
  -- Well-formedness: the three strand labels are in range [1, numEdges].
  (1 ≤ c.e1 ∧ c.e1 ≤ d.numEdges ∧
   1 ≤ c.e2 ∧ c.e2 ≤ d.numEdges ∧
   1 ≤ c.e3 ∧ c.e3 ≤ d.numEdges) ∧
  let c1 := d.colorAtNat coloring c.e1
  let c2 := d.colorAtNat coloring c.e2
  let c3 := d.colorAtNat coloring c.e3
  -- Fox condition: all-equal OR all-pairwise-distinct on the three strands.
  (c1 = c2 ∧ c2 = c3) ∨
  (c1 ≠ c2 ∧ c2 ≠ c3 ∧ c1 ≠ c3)

/-- A valid tricoloring: satisfies the condition at every crossing,
and uses at least 2 colors. -/
def IsTriColoring (d : KnotDiagram) (coloring : TriColoring d) : Prop :=
  (∀ c ∈ d.crossings, triColorConditionAt d (↑coloring) c) ∧
  d.numEdges ≥ 2 ∧ (∃ i j, coloring i ≠ coloring j)
  -- TODO Phase 2: refine once edge indexing is fixed

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
  -- BLOCKED (Phase 5 diagnosis — statement is FALSE under the current move model).
  -- The Phase 4 diagnosis ("remaining blocker = transfer lemma") was INCOMPLETE.
  -- The deeper blocker, established by the certified counter-example below
  -- (`tricolorable_invariant_is_false_under_current_model`), is that the
  -- Reidemeister moves are *too weakly specified* to make the theorem true:
  --
  --   `Reidemeister1 d₁ d₂ := ∃ c : PDCrossing, d₂ = {d₁ with
  --      crossings := d₁.crossings ++ [c], numEdges := d₁.numEdges + 2 } ∨ ...`
  --
  -- The witness `c` is ARBITRARY — its PD labels (e1,e2,e3,e4) are unconstrained.
  -- In particular one may pick `c` with a label OUT of range `[1, numEdges d₂]`,
  -- e.g. `⟨7,8,9,10⟩` when `numEdges d₂ = 8`. Then `triColorConditionAt d₂ _ c`
  -- fails its well-formedness conjunct (`1 ≤ e3 ≤ numEdges` is `1 ≤ 9 ≤ 8` = false),
  -- so `IsTriColoring d₂` is false regardless of the coloring, hence
  -- `IsTricolorable d₂` is false. But `IsTricolorable d₁` (trefoil) is true, so
  -- the biconditional `IsTricolorable d₁ ↔ IsTricolorable d₂` is `(true ↔ false)`
  -- = false, while `ReidemeisterEquiv d₁ d₂` holds (one R1 step). The universal
  -- statement `tricolorable_invariant` is therefore REFUTED by that pair.
  --
  -- What this means for the project: proving `tricolorable_invariant` is NOT a
  -- matter of finding a transfer lemma — the statement must first be made TRUE by
  -- STRENGTHENING the move model. Phase 5 prerequisite (re-modeling):
  --   (1) Replace the symmetric-existential `Reidemeister1/2/3` by constructors
  --       that carry an explicit *geometric edge-renaming*
  --       `Fin d₂.numEdges ↪ Fin d₁.numEdges` (R1: the new curl's two edges
  --       inherit the colour of the strand they sit on; R2: the four new edges
  --       pair up along the two poked strands; R3: a permutation at one crossing).
  --   (2) Add a well-formedness predicate on KnotDiagram (each PD label in
  --       `[1, numEdges]`, each label appears exactly twice) so that malformed
  --       witnesses like `⟨7,8,9,10⟩` are excluded at the type level.
  --   (3) Then re-state `tricolorable_invariant` over the well-formed quotient
  --       and prove the transfer lemma (the original Phase 4 sub-goal) along the
  --       edge-renaming. The ≥2-colours preservation is the delicate case (R1/R2
  --       must not collapse a 3-colouring to a 1-colouring).
  -- Reference: Fox (1962); Adams, "The Knot Book"; for the certified refutation
  -- see `tricolorable_invariant_is_false_under_current_model` below.

/- Certified refutation of `tricolorable_invariant` under the Phase 3 move model.

This is a *positive* diagnostic result (not a gap): it PROVES that the current
symmetric-existential model of Reidemeister moves is too weak to admit the
tricolorability-invariant theorem. The trefoil diagram is tricolorable, but a
single R1 step can reach a diagram whose added crossing has an out-of-range PD
label, which is therefore NOT tricolorable. Since `ReidemeisterEquiv` holds
between them but tricolorability does not transfer, the universal biconditional
fails.

This lemma is the evidence that Phase 5 requires re-modeling the moves (see the
diagnostic on `tricolorable_invariant` above), not merely a transfer lemma. It
is stated and proven below `trefoil_tricolorable` as
`tricolorable_invariant_fails_under_current_model`. -/

/-! ## 3. The trefoil is tricolorable

The trefoil (3_1) can be colored with 3 colors, each crossing seeing
all three colors. This proves the trefoil is NOT the unknot.
-/

theorem trefoil_tricolorable : Knot.isTricolorable trefoil := by
  -- Proof: construct an explicit 3-coloring of the trefoil's 6 arcs (PD labels).
  -- The trefoil PD-code is [[1,4,2,5],[3,6,4,1],[5,2,6,3]], so numEdges = 6.
  -- Fox condition at each crossing on (e1,e2,e3):
  --   c0: (1,4,2), c1: (3,6,4), c2: (5,2,6).
  -- A valid 3-coloring (labels→color, 0-indexed by label-1):
  --   labels {1,2,4} → red, {3,5} → blue, {6} → green.
  -- Check: c0 (1,4,2)→(red,red,red) all-equal ✓
  --        c1 (3,6,4)→(blue,green,red) all-distinct ✓
  --        c2 (5,2,6)→(blue,red,green) all-distinct ✓
  unfold Knot.isTricolorable IsTricolorable IsTriColoring Knot.diagram trefoil
  simp only [trefoilDiagram, triColorConditionAt, KnotDiagram.colorAtNat]
  -- Provide the explicit coloring on Fin 6 (index = label - 1).
  refine' ⟨fun i : Fin 6 =>
              if i.val = 0 ∨ i.val = 1 ∨ i.val = 3 then TriColor.red
              else if i.val = 2 ∨ i.val = 4 then TriColor.blue
              else TriColor.green, _, _, _⟩
  -- Crossing condition: each of the 3 crossings satisfies the Fox condition.
  · -- The three crossings are ⟨1,4,2,5⟩, ⟨3,6,4,1⟩, ⟨5,2,6,3⟩. Decide by computation.
    intro c hc
    -- Reduce membership in the explicit crossing list to the 3 concrete cases.
    match c with
    | ⟨1, 4, 2, 5⟩ => decide
    | ⟨3, 6, 4, 1⟩ => decide
    | ⟨5, 2, 6, 3⟩ => decide
  -- numEdges ≥ 2: literal 6 ≥ 2
  · decide
  -- At least 2 colors: edge 0 = red, edge 2 = blue, red ≠ blue
  · exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩

/-! ## 3b. Certified counter-example: the invariant theorem needs a stronger model

This is a *positive* diagnostic result (not a gap). It PROVES that the current
symmetric-existential model of Reidemeister moves (Phase 3) is too weak to admit
the tricolorability-invariant theorem `tricolorable_invariant` stated in §2.

The trefoil diagram is tricolorable (proven just above), but a single R1 step
can reach a diagram whose added crossing has an out-of-range PD label, which is
therefore NOT tricolorable. Since `ReidemeisterEquiv` holds between them but
tricolorability does not transfer, any universal biconditional
`∀ d₁ d₂, ReidemeisterEquiv d₁ d₂ → IsTricolorable d₁ ↔ IsTricolorable d₂`
is refuted by that pair. See the diagnostic on `tricolorable_invariant` (§2) for
the Phase 5 prerequisite: re-model the moves with explicit geometric edge-
renaming + a well-formedness predicate, so that malformed witnesses like the
`⟨7,8,9,10⟩` below are excluded at the type level. -/
theorem tricolorable_invariant_fails_under_current_model :
    ∃ (d₁ d₂ : KnotDiagram),
      ReidemeisterEquiv d₁ d₂ ∧
      IsTricolorable d₁ ∧
      ¬ IsTricolorable d₂ := by
  -- Counter-example pair: d₁ = trefoilDiagram (tricolorable, proven above), and
  -- d₂ = trefoilDiagram with one malformed crossing ⟨7,8,9,10⟩ appended and
  -- numEdges = 6 + 2 = 8. A single R1 step connects them (existential witness
  -- c = ⟨7,8,9,10⟩), but d₂ is NOT tricolorable because the added crossing
  -- fails the label-range well-formedness conjunct of `triColorConditionAt`
  -- (e3 = 9 > numEdges d₂ = 8).
  refine' ⟨trefoilDiagram,
           { crossings := trefoilDiagram.crossings ++ [⟨7, 8, 9, 10⟩]
             numEdges := trefoilDiagram.numEdges + 2
             hwell := by trivial }, ?_, ?_, ?_⟩
  -- (a) ReidemeisterEquiv d₁ d₂ holds: one R1 step with witness ⟨7,8,9,10⟩.
  · exact ReidemeisterEquiv.step (ReidemeisterStep.r1
      ⟨⟨7, 8, 9, 10⟩, Or.inl rfl⟩)
  -- (b) d₁ (the trefoil) is tricolorable: `trefoil_tricolorable` proves
  -- `Knot.isTricolorable trefoil`, which is definitionally
  -- `IsTricolorable trefoil.diagram = IsTricolorable trefoilDiagram`.
  · exact trefoil_tricolorable
  -- (c) d₂ is NOT tricolorable: any coloring fails the Fox condition at the
  -- malformed crossing ⟨7,8,9,10⟩, because e3 = 9 > numEdges d₂ = 8.
  · rintro ⟨coloring, hcond, hedges, htwocolors⟩
    -- The malformed crossing is in d₂.crossings (it was appended).
    have hmem : (⟨7, 8, 9, 10⟩ : PDCrossing) ∈
        (trefoilDiagram.crossings ++ [⟨7, 8, 9, 10⟩]) := by
      simp [List.mem_append]
    -- The Fox condition must hold at every crossing, including the malformed one.
    have hfox := hcond ⟨7, 8, 9, 10⟩ hmem
    -- But its well-formedness conjunct requires 1 ≤ e3 = 9 ≤ numEdges d₂ = 8,
    -- i.e. 9 ≤ 8, which is false. Extract the well-formedness half and close.
    -- hfox : (1≤7 ∧ 7≤n ∧ 1≤8 ∧ 8≤n ∧ 1≤9 ∧ 9≤n) ∧ (Fox disjunction)
    have hwf := hfox.1
    -- hwf : 1 ≤ 7 ∧ 7 ≤ trefoilDiagram.numEdges + 2 ∧
    --        1 ≤ 8 ∧ 8 ≤ trefoilDiagram.numEdges + 2 ∧
    --        1 ≤ 9 ∧ 9 ≤ trefoilDiagram.numEdges + 2
    -- trefoilDiagram.numEdges = 6 by definition, so the last conjunct is 9 ≤ 8.
    simp only [trefoilDiagram] at hwf   -- reduces numEdges to 6, then 6 + 2 = 8
    omega

/-! ## 4. The unknot is NOT tricolorable

The unknot has a diagram with no crossings. Any coloring uses only
one strand, so the "at least 2 colors" condition fails.
-/

theorem unknot_not_tricolorable : ¬ Knot.isTricolorable unknot := by
  -- Proof: unknot has exactly 1 edge (numEdges = 1).
  -- Fin 1 has a single element ⟨0, _⟩, so every coloring is constant.
  -- Hence ∃ i j, coloring i ≠ coloring j is impossible.
  unfold Knot.isTricolorable IsTricolorable IsTriColoring
  rintro ⟨coloring, hcond, hedges, htwocolors⟩
  -- htwocolors : ∃ i j, coloring i ≠ coloring j
  -- But Fin 1 has only one element, contradiction
  have : ∀ (i j : Fin 1), coloring i = coloring j := by
    intro i j
    -- Fin 1 has only ⟨0, _⟩
    have hi : i = ⟨0, by omega⟩ := by exact Fin.ext_iff.mpr (Fin.val_eq_zero i)
    have hj : j = ⟨0, by omega⟩ := by exact Fin.ext_iff.mpr (Fin.val_eq_zero j)
    rw [hi, hj]
  obtain ⟨i, j, hne⟩ := htwocolors
  exact hne (this i j)

/-! ## 5. Corollary: the trefoil is not the unknot

Since tricolorability is an invariant, and the trefoil has it
but the unknot doesn't, they are different knots.
-/

theorem trefoil_not_unknot : ¬ KnotEquiv trefoil unknot := by
  intro h
  -- If trefoil ≈ unknot, then trefoil tricolorable ↔ unknot tricolorable
  -- But trefoil IS tricolorable and unknot IS NOT → contradiction
  -- Sketch: have := (tricolorable_invariant trefoilDiagram unknotDiagram h).mp
  --            trefoil_tricolorable
  --         exact unknot_not_tricolorable this
  exact sorry
  -- BLOCKED (Phase 4 update): the natural route (tricolorable_invariant +
  -- trefoil_tricolorable + unknot_not_tricolorable) is gated by
  -- tricolorable_invariant (this file), whose remaining blocker is the transfer
  -- lemma across Reidemeister moves (see the diagnostic there). The two pieces
  -- it composes — `trefoil_tricolorable` and `unknot_not_tricolorable` — are
  -- now both proven under the real Fox condition, so once the invariant lands
  -- this corollary follows by the sketch above.
  -- Alternative route attempted: prove ¬KnotEquiv directly by showing the diagrams
  -- cannot be Reidemeister-equivalent. Reidemeister1/2/3 are concrete, but
  -- ReidemeisterEquiv is the RTC of those steps; to show two diagrams are NOT
  -- connected one must classify all diagrams reachable from trefoilDiagram —
  -- out of reach without a normalisation invariant (e.g. crossing-number
  -- monotonicity under the moves, itself needing the true minimal crossing number).
  -- Dependency: tricolorable_invariant (→ transfer lemma across moves).

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
  -- Proof: under the Phase 3 provisional definition, crossingNumber equals
  -- crossingNumberOfDiagram, which counts the trefoil diagram's crossings.
  -- The standard trefoil PD-code has exactly 3 crossings.
  show trefoil.crossingNumberOfDiagram = 3
  unfold Knot.crossingNumberOfDiagram Knot.diagram trefoil trefoilDiagram
  decide

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
  -- BLOCKED: requires substantial infrastructure not yet in the project:
  --   1. Crossing change operation on KnotDiagram (changeCrossing exists but no
  --      well-formedness proof that the result is a valid diagram)
  --   2. Minimization over equivalence classes (Knot.crossingNumber has same issue)
  --   3. Reachability in a graph of diagrams
  -- Phase 4+ target — out of scope for Phase 2

end Knots

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
  -- BLOCKED (Phase 5 — model STILL too coarse after PR1). PR1 (#2929)
  -- strengthened the move model with `KnotDiagram.wf` on both diagrams and an
  -- edge-renaming `ρ`. That REMOVED the Phase-3 obstruction (malformed witness
  -- `⟨7,8,9,10⟩`, excluded by `wf`), but it did NOT make this statement true.
  -- A SECOND certified counter-example — `tricolorable_invariant_fails_under_pr1_model`
  -- below (§3b) — proves the biconditional is STILL REFUTED under the PR1 model.
  --
  -- Root cause (the real blocker): `wf`'s "every label appears exactly twice"
  -- condition forces an R1-twist's new crossing `c` to use ONLY the two fresh
  -- edges `{n+1, n+2}` (labels `1..n` already appear twice in `d₁`, so `c`
  -- cannot reuse any without breaking the parity), and `ρ` is a FREE injection
  -- not tied to `c`'s labels. The new crossing's Fox condition is therefore
  -- DECOUPLED from `d₁`'s coloring — a twist can CREATE tricolorability from
  -- nothing (or hide the ≥2-colours entirely in the fresh edges while `d₁` is
  -- forced monochrome). The fix is NOT a transfer lemma but a STRONGER
  -- constructor model in which `ρ` DETERMINES `c`'s labels: a genuine R1 curl
  -- on arc `a` is `⟨a, a, n+1, n+2⟩` (one strand is the EXISTING arc `a`),
  -- whose Fox condition ties the new edges to `color a`. See §3b for the
  -- witness and the Phase-5 prerequisite. Reference: Fox (1962); Adams, "The
  -- Knot Book".

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

/-! ## 3b. Certified counter-example: `tricolorable_invariant` is STILL FALSE
under the Phase 5 PR1 move model.

This is a *positive* diagnostic result (not a gap). PR1 (#2929) re-modeled
`Reidemeister1/2/3` to require `KnotDiagram.wf` on both diagrams, which excluded
the *malformed-witness* counter-example of the Phase 3 model (a crossing
`⟨7,8,9,10⟩` with labels out of `[1, numEdges]`). But the re-modeling is still
too coarse to make `tricolorable_invariant` TRUE.

Why. The `wf` "every label appears exactly twice" condition forces an R1-twist's
new crossing `c` to use ONLY the two fresh edges `{n+1, n+2}` — labels `1..n`
already appear twice in `d₁`, so `c` cannot reuse any of them without breaking
parity. Moreover the edge-renaming `ρ : Fin (min) ↪ Fin (max)` introduced by
PR1 is a FREE injection, NOT tied to `c`'s labels. The new crossing's Fox
condition therefore involves only the two fresh (freely-colorable) edges and is
DECOUPLED from `d₁`'s coloring — so a twist can CREATE tricolorability out of
nothing, or symmetrically hide the ≥2-colours entirely in the fresh edges while
`d₁` is forced monochrome.

Witness (refutes the universal biconditional):
  d₁ = { crossings := [⟨1,2,1,2⟩], numEdges := 2 }    — NOT tricolorable.
       Fox at ⟨1,2,1,2⟩ reads (coloring⟨0⟩, coloring⟨1⟩, coloring⟨0⟩), which is
       all-equal ONLY if coloring⟨0⟩ = coloring⟨1⟩ — contradicting the ≥2-colours
       requirement. So no valid tricoloring exists.
  d₂ = { crossings := [⟨1,2,1,2⟩, ⟨3,4,3,4⟩], numEdges := 4 }  — tricolorable.
       Color edges 1,2 = red and 3,4 = blue: Fox holds at both crossings
       (all-equal within each), and ≥2 colours are used.
  A single R1 twist step connects them (`ReidemeisterEquiv d₁ d₂`), so the
  biconditional `IsTricolorable d₁ ↔ IsTricolorable d₂` is `(false ↔ true)`.

**Phase 5 prerequisite (the real fix).** Tie the edge-renaming to the crossing:
make the move constructors carry the geometric splicing so that `ρ` DETERMINES
`c`'s labels — a genuine R1 curl on arc `a` is `⟨a, a, n+1, n+2⟩` (one strand is
the EXISTING arc `a`), whose Fox condition constrains the new edges to inherit
`color a`, which is what makes tricolorability transfer along `ρ`. Then
re-prove the transfer lemma. Reference: Fox (1962); Adams, "The Knot Book". -/

theorem tricolorable_invariant_fails_under_pr1_model :
    ∃ (d₁ d₂ : KnotDiagram),
      ReidemeisterEquiv d₁ d₂ ∧
      ¬ IsTricolorable d₁ ∧
      IsTricolorable d₂ := by
  -- Witness pair.
  refine' ⟨{ crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial },
           { crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4, hwell := by trivial },
           ?_, ?_, ?_⟩
  -- (a) ReidemeisterEquiv d₁ d₂: a single R1 twist step, witness c = ⟨3,4,3,4⟩.
  --     d₁ = {[⟨1,2,1,2⟩], numEdges = 2}; d₂ = {[⟨1,2,1,2⟩, ⟨3,4,3,4⟩], numEdges = 4}.
  · refine' ReidemeisterEquiv.step (ReidemeisterStep.r1 ?_)
    refine' ⟨?_, ?_, ⟨⟨3, 4, 3, 4⟩, ⟨?_, ?_⟩⟩⟩
    · -- d₁.wf = true: labels 1,2 each appear twice across [1,2,1,2].
      decide
    · -- d₂.wf = true: labels 1,2,3,4 each appear twice across [1,2,1,2,3,4,3,4].
      decide
    · -- ρ : Fin (min d₁.numEdges d₂.numEdges) ↪ Fin (max d₁.numEdges d₂.numEdges),
      --   which is defeq to Fin 2 ↪ Fin 4 (d₁.numEdges = 2, d₂.numEdges = 4 reduce,
      --   and min/max on the literals reduce). Constructed concretely as Fin 2 ↪ Fin 4
      --   so omega sees concrete bounds; `exact` discharges the defeq to the goal type.
      have ρ : Fin 2 ↪ Fin 4 :=
        ⟨fun i => ⟨i.val, by omega⟩,
         fun a b h => by
           have h : (⟨a.val, by omega⟩ : Fin 4) = ⟨b.val, by omega⟩ := h
           injection h with hval
           exact Fin.ext hval⟩
      exact ρ
    · -- surgery (twist arm): d₂ = { d₁ with crossings := d₁.crossings ++ [⟨3,4,3,4⟩], numEdges := d₁.numEdges + 2 }.
      left
      rfl
  -- (b) d₁ is NOT tricolorable: Fox at the sole crossing ⟨1,2,1,2⟩ forces the two
  --     edges to the same colour, contradicting the ≥2-colours requirement.
  · show ¬ IsTricolorable { crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial }
    rintro ⟨coloring, hcond, hedges, htwo⟩
    -- The sole crossing ⟨1,2,1,2⟩ is in d₁.crossings; apply the Fox condition to it.
    have hfox := hcond (⟨1, 2, 1, 2⟩ : PDCrossing)
        (by exact List.mem_cons_self : _ ∈ ([⟨1, 2, 1, 2⟩] : List PDCrossing))
    -- Unfold: at ⟨1,2,1,2⟩ with numEdges = 2, the colours read are coloring⟨0⟩ (label 1)
    -- and coloring⟨1⟩ (label 2). Fox's all-distinct branch is impossible (the third
    -- strand equals the first), so Fox forces coloring⟨0⟩ = coloring⟨1⟩.
    have h01 : coloring ⟨0, by decide⟩ = coloring ⟨1, by decide⟩ := by
      have h := hfox
      simp only [triColorConditionAt, KnotDiagram.colorAtNat] at h
      rcases h with ⟨_, h | h⟩
      · exact h.1
      · -- all-distinct branch: needs c1 ≠ c3, but e1 = e3 = 1 makes c1 ≡ c3 (rfl) → contradiction.
        exact (h.2.2 rfl).elim
    -- Hence every Fin 2 colour equals coloring⟨0⟩ (the only two elements are 0, 1).
    have hAll : ∀ (i : Fin 2), coloring i = coloring ⟨0, by decide⟩ := by
      intro i
      have h : i.val = 0 ∨ i.val = 1 := by omega
      rcases h with h | h
      · rw [show i = (⟨0, by omega⟩ : Fin 2) from Fin.ext h]
      · rw [show i = (⟨1, by omega⟩ : Fin 2) from Fin.ext h, h01]
    obtain ⟨i, j, hne⟩ := htwo
    exact hne (by rw [hAll i, hAll j])
  -- (c) d₂ IS tricolorable: edges 1,2 (Fin index 0,1) = red, edges 3,4 (index 2,3) = blue;
  --     Fox is all-equal within each crossing, ≥2 colours used.
  · show IsTricolorable { crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4, hwell := by trivial }
    refine' ⟨fun i : Fin 4 => if i.val ≤ 1 then TriColor.red else TriColor.blue, ?_, ?_, ?_⟩
    · -- Fox at every crossing of d₂.
      intro c hc
      -- d₂.crossings = [⟨1,2,1,2⟩, ⟨3,4,3,4⟩]; hc pins c to one of them.
      have hsplit : c = ⟨1, 2, 1, 2⟩ ∨ c = ⟨3, 4, 3, 4⟩ := by simpa using hc
      rcases hsplit with rfl | rfl
      · -- c = ⟨1,2,1,2⟩: local strands (1,2,1) all red → all-equal.
        simp only [triColorConditionAt, KnotDiagram.colorAtNat]; decide
      · -- c = ⟨3,4,3,4⟩: local strands (3,4,3) all blue → all-equal.
        simp only [triColorConditionAt, KnotDiagram.colorAtNat]; decide
    · -- numEdges = 4 ≥ 2.
      decide
    · -- ≥2 colours: edge index 0 = red ≠ blue = edge index 2.
      exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩

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

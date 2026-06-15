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

/-! ## 3c. Non-regression gate (PR1.5): the #2938 witness is EXCLUDED under `Reidemeister1'`

`Reidemeister1'` (Reidemeister.lean, PR1.5 #2956) is the ρ-determined strengthening
of the R1 move: the new crossing is forced to the shape `⟨a, a, n+1, n+2⟩` — one
strand is the existing arc `a`. This couples the two fresh edges to `color(a)` via
the Fox condition, which is what the PR1 free-`ρ` model lacked.

The certified counter-example `tricolorable_invariant_fails_under_pr1_model`
above (§3b) refutes the biconditional *under the PR1 model* by exhibiting a
specific witness pair `(d₁, d₂)` connected by a PR1 R1-step. **This theorem proves
that very witness pair is NOT connected by a `Reidemeister1'` step** — i.e. the
ρ-determined refinement excludes the counter-example by construction. This is the
non-regression test ai-01 required (PR1.5 gate 1, dashboard 11:35Z): the re-model
must EXCLUDE #2938, and here we prove it explicitly.

Witness pair (same as §3b):
  d₁ = { crossings := [⟨1,2,1,2⟩], numEdges := 2 }
  d₂ = { crossings := [⟨1,2,1,2⟩, ⟨3,4,3,4⟩], numEdges := 4 }

Why `Reidemeister1' d₁ d₂` fails:
  - Twist arm forces `d₂.crossings = [⟨1,2,1,2⟩] ++ [⟨a, a, 3, 4⟩]`, i.e. the
    second crossing must be `⟨a, a, 3, 4⟩`. But `d₂`'s second crossing is
    `⟨3, 4, 3, 4⟩`, so list equality forces `⟨3,4,3,4⟩ = ⟨a,a,3,4⟩`, giving
    `a = 3` (from e1) and `a = 4` (from e2) — contradiction.
  - Untwist arm forces `d₁.crossings` to equal `d₂.crossings ++ [⟨a,a,_,_⟩]`,
    a 3-element list, but `d₁.crossings` has 1 element — length contradiction.
-/

/-- The #2938 witness pair is NOT connected by a ρ-determined R1 move
(`Reidemeister1'`). This is the PR1.5 non-regression gate: the re-model excludes
the counter-example by construction. -/
theorem pr1_counterexample_excluded_under_rho_determined :
    ¬ Reidemeister1'
        { crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial }
        { crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4, hwell := by trivial } := by
  -- Unfold Reidemeister1': wf₁ ∧ wf₂ ∧ (∃ a, range ∧ (∃ ρ, surgery ∨ surgery)).
  rintro ⟨_hwf₁, _hwf₂, a, _hrange₁, _hrange₂, _ρ, hsurg⟩
  rcases hsurg with ht | ht
  · -- TWIST arm: d₂ = { d₁ with crossings := d₁.crossings ++ [⟨a,a,3,4⟩], numEdges := 4 }.
    -- d₁.numEdges = 2, so the appended crossing is ⟨a, a, 3, 4⟩.
    -- Project .crossings off the record equality ht by congruence, then the RHS
    -- ({ d₁ with crossings := X }).crossings reduces to X = d₁.crossings ++ [⟨a,a,3,4⟩].
    have hfield :
        ({ crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4, hwell := by trivial }
          : KnotDiagram).crossings =
        ({ crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial }
          : KnotDiagram).crossings ++ [⟨a, a, 3, 4⟩] :=
      congrArg (·.crossings) ht
    -- The RHS reduces to [⟨1,2,1,2⟩] ++ [⟨a,a,3,4⟩]; second elements: ⟨3,4,3,4⟩ = ⟨a,a,3,4⟩.
    have h2nd : (⟨3, 4, 3, 4⟩ : PDCrossing) = ⟨a, a, 3, 4⟩ := by
      simpa [List.append] using hfield
    -- Injectivity of PDCrossing (4 fields): e1 gives 3 = a, e2 gives 4 = a.
    injection h2nd with h_e1 h_e2 h_e3 h_e4
    omega
  · -- UNTWIST arm: d₁ = { d₂ with crossings := d₂.crossings ++ [⟨a,a,5,6⟩], numEdges := 6 }.
    -- d₂.numEdges = 4, so appended crossing = ⟨a, a, 5, 6⟩.
    -- Project .crossings off the record equality by congruence (term-mode, robust
    -- against literal-form mismatch that blocks `subst`/`rw`).
    have hfield :
        ({ crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial }
          : KnotDiagram).crossings =
        ({ crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4, hwell := by trivial }
          : KnotDiagram).crossings ++ [⟨a, a, 5, 6⟩] :=
      congrArg (·.crossings) ht
    -- Length contradiction: LHS has length 1, RHS has length 3.
    -- `simp at h` reduces the list lengths to concrete numbers (`1` and `3`),
    -- then closes the goal by deriving `False` from the contradiction `1 = 3`.
    have h := congrArg List.length hfield
    simp at h

/-! ## 3d. The connected R1 move (option C) PRESERVES tricolorability on the witness

This is the positive complement to the PR1 counter-example (§3b). Under the
STRENGTHENED `Reidemeister1Connected` (option C, carrying the `Y'.isRenameOf`
hypothesis), the connected R1 twist does NOT create or destroy tricolorability
the way the disjoint-kink append model did (#2938). We verify this on the concrete
witness pair of `reidemeister1Connected_satisfiable` (Reidemeister.lean): the
connected move maps a tricolorable `d₁` to a tricolorable `d₂`, and conversely.

Why both directions hold on the witness. The connected twist on arc `a = 1`
renames the `e1` slot of crossing 1 (`1 → 5 = b`) and appends `C = ⟨1,5,6,6⟩`.
A tricoloring of `d₁` extends to `d₂` by giving the two new edges `b = 5` and
`c = 6` the colour of the arc `a = 1`: then the new crossing `C` reads
`(col a, col a, col a)` — all-equal, Fox-trivial — and the modified crossing
reads the same three colours as before (the renamed slot `b` carries `col a`).
Conversely a tricoloring of `d₂` projects back to `d₁`. This is the
*computational* verification that option C preserves the invariant; the general
transfer lemma (`Reidemeister1Connected.tricolorable_invariant`, the PR2 target)
makes this argument for arbitrary diagrams — gated on the strengthened def
merging (PR #2990).

Certified constructively: we exhibit an explicit 3-colouring of each diagram
(mirroring the `trefoil_tricolorable` pattern), so each side is inhabited and the
biconditional reduces to `(true ↔ true)`. `IsTricolorable` is an existential over
`Fin n → TriColor`, so no `Decidable` instance auto-derives — the colourings are
supplied by hand, with each crossing's Fox condition discharged by `decide`.
-/

/-- The witness `d₁` of `reidemeister1Connected_satisfiable` (Reidemeister.lean). -/
def witnessD1Connected : KnotDiagram :=
  { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4, hwell := by trivial }

/-- The witness `d₂` of `reidemeister1Connected_satisfiable` (Reidemeister.lean). -/
def witnessD2Connected : KnotDiagram :=
  { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], numEdges := 6, hwell := by trivial }

/-- `witnessD1Connected` is tricolorable: both crossings are `⟨1,2,3,4⟩`, each
    reading `(red, blue, green)` on the Fox strands `(e1, e2, e3) = (1, 2, 3)`
    (all pairwise distinct). Constructive, mirroring `trefoil_tricolorable`. -/
theorem witnessD1Connected_tricolorable : IsTricolorable witnessD1Connected := by
  unfold IsTricolorable IsTriColoring witnessD1Connected
  simp only [triColorConditionAt, KnotDiagram.colorAtNat]
  refine' ⟨fun i : Fin 4 =>
              if i.val = 0 then TriColor.red
              else if i.val = 1 then TriColor.blue
              else if i.val = 2 then TriColor.green
              else TriColor.red, ?_, ?_, ?_⟩
  · intro c hc
    -- Both crossings are `⟨1,2,3,4⟩`; the single distinct value is the only
    -- element of the list, so the Fox condition is checked once by computation.
    match c with
    | ⟨1, 2, 3, 4⟩ => decide
  · decide
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩

/-- `witnessD2Connected` is tricolorable: the original crossings `⟨1,2,3,4⟩`
    and `⟨5,2,3,4⟩` read all-distinct colours, and the new kink `⟨1,5,6,6⟩`
    reads `(red, red, red)` (all-equal, Fox-trivial). The two new edges `b = 5`
    and `c = 6` carry the colour of arc `a = 1` (red), so the twist does not
    create or destroy tricolorability. -/
theorem witnessD2Connected_tricolorable : IsTricolorable witnessD2Connected := by
  unfold IsTricolorable IsTriColoring witnessD2Connected
  simp only [triColorConditionAt, KnotDiagram.colorAtNat]
  refine' ⟨fun i : Fin 6 =>
              if i.val = 0 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 then TriColor.red
              else if i.val = 1 then TriColor.blue
              else TriColor.green, ?_, ?_, ?_⟩
  · intro c hc
    match c with
    | ⟨1, 2, 3, 4⟩ => decide
    | ⟨5, 2, 3, 4⟩ => decide
    | ⟨1, 5, 6, 6⟩ => decide
  · decide
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩

/-- The connected R1 move (option C, strengthened `Reidemeister1Connected`)
    preserves tricolorability on the concrete witness pair of
    `reidemeister1Connected_satisfiable`: both `witnessD1Connected` and
    `witnessD2Connected` are tricolorable, so the biconditional is
    `(true ↔ true)`. This is the positive complement to the PR1 counter-example
    `tricolorable_invariant_fails_under_pr1_model` (§3b), confirming the
    connected-surgery model does not share the disjoint-kink defect. Proved
    constructively (explicit 3-colourings, mirroring `trefoil_tricolorable`). -/
theorem reidemeister1Connected_witness_preserves_tricolorable :
    IsTricolorable witnessD1Connected ↔ IsTricolorable witnessD2Connected :=
  ⟨fun _ => witnessD2Connected_tricolorable, fun _ => witnessD1Connected_tricolorable⟩

/-! ## 3e. PR2 forward transfer: a connected R1 move PRESERVES tricolorability

Under the strengthened `Reidemeister1Connected` (carrying the `Y'.isRenameOf`
hypothesis, merged #2990), a tricoloring of `d₁` extends to a tricoloring of
`d₂`: the two fresh edges `b = numEdges+1` and `c = numEdges+2` both carry the
colour of arc `a`. This makes the new kink crossing `⟨a, b, c, c⟩` Fox-trivial
(`(col a)³`, all-equal) and the `a → b` rename Fox-invisible (`col₂ b = col₁ a`).
This is the forward half of `tricolorable_invariant` specialised to the
connected R1 move (option C).
-/

/-- Forward membership for `List.set`: an element of `l.set n v` is either the
    inserted value `v` (at the modified position) or already an element of `l`.
    Pure list-combinatorics helper (no knot content), used by the transfer lemma
    to split `d₂.crossings = d₁.crossings.set i Y' ++ [C]`. -/
private theorem mem_set_fwd {α : Type*} : ∀ (n : Nat) (l : List α) (v c : α),
    c ∈ l.set n v → c = v ∨ c ∈ l
  | 0, [], _, _, h => by simp at h
  | 0, hd :: tl, v, c, h => by
    change c ∈ v :: tl at h
    simp only [List.mem_cons] at h ⊢
    rcases h with heq | hmem
    · refine Or.inl ?_; exact heq
    · exact Or.inr (Or.inr hmem)
  | _+1, [], _, _, h => by simp at h
  | n+1, hd :: tl, v, c, h => by
    have ih := mem_set_fwd n tl v c
    change c ∈ hd :: tl.set n v at h
    simp only [List.mem_cons] at h ⊢
    rcases h with hhd | hset
    · exact Or.inr (Or.inl hhd)
    · rcases ih hset with rfl | hmem
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hmem)

theorem Reidemeister1Connected.tricolorable_forward {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) (htri : IsTricolorable d₁) :
    IsTricolorable d₂ := by
  obtain ⟨_hwf₁, _hwf₂, i, a, Y', _ρ, ha1, ha2, _hamem, _hproper, hrename, hsurg⟩ := h
  -- Edge-count and crossing-list consequences of the surgery equation.
  have hd₂num : d₂.numEdges = d₁.numEdges + 2 := by
    simpa using congrArg (·.numEdges) hsurg
  have hd₂cross : d₂.crossings =
      d₁.crossings.set i.val Y' ++
        [⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩] := by
    simpa using congrArg (·.crossings) hsurg
  obtain ⟨col₁, hfox₁, hge2, h2col⟩ := htri
  -- Extension colouring: preserved edges keep their colour, the two new edges
  -- (indices `d₁.numEdges` and `d₁.numEdges+1`, i.e. labels `b`, `c`) carry
  -- `col₁ a`. Defined as a local def so `simp only [col₂]` can unfold it.
  have haim1 : a - 1 < d₁.numEdges := by omega
  have hd₂ge₁ : d₁.numEdges ≤ d₂.numEdges := by omega
  -- Embedding of `d₁`'s edge indices into `d₂`'s (the +2 fresh edges sit above).
  let emb : Fin d₁.numEdges → Fin d₂.numEdges :=
    fun k => ⟨k.val, Nat.lt_of_lt_of_le k.isLt hd₂ge₁⟩
  let col₂ : Fin d₂.numEdges → TriColor :=
    fun j => if hj : j.val < d₁.numEdges then col₁ ⟨j.val, hj⟩
             else col₁ ⟨a - 1, haim1⟩
  refine' ⟨col₂, ?fox, ?num, ?col⟩
  case num =>
    -- `d₂.numEdges = d₁.numEdges + 2 ≥ 2` since `d₁.numEdges ≥ 2`.
    omega
  case col =>
    -- At least two colours: two distinct-coloured edges of `d₁` embed into `d₂`.
    obtain ⟨p, q, hpq⟩ := h2col
    -- `col₂ (emb k) = col₁ k`: beta-reduce, the `if` is positive (k.val < n),
    -- and the `Fin` constructor collapses by proof irrelevance.
    have hcol_pres : ∀ k : Fin d₁.numEdges, col₂ (emb k) = col₁ k := by
      intro k
      conv_lhs => unfold col₂
      rw [dif_pos k.isLt]
    refine' ⟨emb p, emb q, ?_⟩
    rw [hcol_pres p, hcol_pres q]
    exact hpq
  case fox =>
    -- Colour-preservation facts, the heart of the transfer.
    -- (F1) A preserved label `l` (1 ≤ l ≤ d₁.numEdges) reads the same colour in
    --      `d₂` (under `col₂`) as in `d₁` (under `col₁`).
    have hcolF1 : ∀ l, 1 ≤ l → l ≤ d₁.numEdges →
        d₂.colorAtNat col₂ l = d₁.colorAtNat col₁ l := by
      intro l hl1 hln
      have hn0d₂ : d₂.numEdges ≠ 0 := by omega
      have hn0d₁ : d₁.numEdges ≠ 0 := by omega
      have hL : d₂.colorAtNat col₂ l =
          col₂ ⟨(l - 1) % d₂.numEdges, Nat.mod_lt (l - 1) (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
      have hR : d₁.colorAtNat col₁ l =
          col₁ ⟨(l - 1) % d₁.numEdges, Nat.mod_lt (l - 1) (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₁]
      rw [hL, hR]
      simp only [hd₂num]
      have h1 : (l - 1) % (d₁.numEdges + 2) = l - 1 := Nat.mod_eq_of_lt (by omega)
      have h2 : (l - 1) % d₁.numEdges = l - 1 := Nat.mod_eq_of_lt (by omega)
      simp only [h1, h2]
      conv_lhs => unfold col₂
      simp only [dif_pos (by omega : (l - 1) < d₁.numEdges)]
    have hcolF2b : d₂.colorAtNat col₂ (d₁.numEdges + 1) = d₁.colorAtNat col₁ a := by
      have hn0d₂ : d₂.numEdges ≠ 0 := by omega
      have hn0d₁ : d₁.numEdges ≠ 0 := by omega
      have hL : d₂.colorAtNat col₂ (d₁.numEdges + 1) =
          col₂ ⟨(d₁.numEdges + 1 - 1) % d₂.numEdges, Nat.mod_lt (d₁.numEdges + 1 - 1) (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
      have hR : d₁.colorAtNat col₁ a =
          col₁ ⟨(a - 1) % d₁.numEdges, Nat.mod_lt _ (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₁]
      rw [hL, hR]
      simp only [hd₂num]
      have h1 : (d₁.numEdges + 1 - 1) % (d₁.numEdges + 2) = d₁.numEdges := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have h2 : (a - 1) % d₁.numEdges = a - 1 := Nat.mod_eq_of_lt (by omega)
      simp only [h1, h2]
      conv_lhs => unfold col₂
      simp only [dif_neg (by omega : ¬(d₁.numEdges < d₁.numEdges))]
    have hcolF2c : d₂.colorAtNat col₂ (d₁.numEdges + 2) = d₁.colorAtNat col₁ a := by
      have hn0d₂ : d₂.numEdges ≠ 0 := by omega
      have hn0d₁ : d₁.numEdges ≠ 0 := by omega
      have hL : d₂.colorAtNat col₂ (d₁.numEdges + 2) =
          col₂ ⟨(d₁.numEdges + 2 - 1) % d₂.numEdges, Nat.mod_lt (d₁.numEdges + 2 - 1) (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
      have hR : d₁.colorAtNat col₁ a =
          col₁ ⟨(a - 1) % d₁.numEdges, Nat.mod_lt _ (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₁]
      rw [hL, hR]
      simp only [hd₂num]
      have h1 : (d₁.numEdges + 2 - 1) % (d₁.numEdges + 2) = d₁.numEdges + 1 := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have h2 : (a - 1) % d₁.numEdges = a - 1 := Nat.mod_eq_of_lt (by omega)
      simp only [h1, h2]
      conv_lhs => unfold col₂
      simp only [dif_neg (by omega : ¬(d₁.numEdges + 1 < d₁.numEdges))]
    -- ===== Forward Fox transfer: ∀ c ∈ d₂.crossings, triColorConditionAt d₂ col₂ c.
    -- We only unfold `triColorConditionAt` (NOT `colorAtNat`), so the Fox part keeps
    -- `colorAtNat` folded and the colour lemmas hcolF1/hcolF2b/hcolF2c fire by `rw`.
    -- (C) New kink ⟨a, n+1, n+2, n+2⟩: strands (a, n+1, n+2) all read `col₁ a`.
    have hC : triColorConditionAt d₂ col₂
        ⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩ := by
      simp only [triColorConditionAt]
      refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, ?_⟩
      left
      refine ⟨?_, ?_⟩
      · rw [hcolF1 a ha1 ha2, hcolF2b]
      · rw [hcolF2b, hcolF2c]
    -- (iii) An unchanged crossing inherits d₁'s Fox: each preserved strand reads the
    --       same colour under `col₂` (via hcolF1), so the Fox condition is identical.
    have h_inherit : ∀ c, c ∈ d₁.crossings → triColorConditionAt d₂ col₂ c := by
      intro c hcmem
      have hfc : triColorConditionAt d₁ col₁ c := hfox₁ c hcmem
      simp only [triColorConditionAt] at hfc ⊢
      obtain ⟨⟨he11, he12, he21, he22, he31, he32⟩, hfox⟩ := hfc
      refine ⟨⟨he11, by omega, he21, by omega, he31, by omega⟩, ?_⟩
      have h1 : d₂.colorAtNat col₂ c.e1 = d₁.colorAtNat col₁ c.e1 := hcolF1 c.e1 he11 he12
      have h2 : d₂.colorAtNat col₂ c.e2 = d₁.colorAtNat col₁ c.e2 := hcolF1 c.e2 he21 he22
      have h3 : d₂.colorAtNat col₂ c.e3 = d₁.colorAtNat col₁ c.e3 := hcolF1 c.e3 he31 he32
      rcases hfox with ⟨h12, h23⟩ | ⟨h12, h23, h13⟩
      · left; refine ⟨?_, ?_⟩
        · rw [h1, h2]; exact h12
        · rw [h2, h3]; exact h23
      · right; refine ⟨?_, ?_, ?_⟩
        · rw [h1, h2]; exact h12
        · rw [h2, h3]; exact h23
        · rw [h1, h3]; exact h13
    -- (ii) The modified endpoint Y' preserves Fox: `isRenameOf` makes each strand of
    --       Y' read the same colour as the corresponding strand of the original crossing
    --       under `col₁` (unchanged strand via hcolF1; renamed `a→b` strand via hcolF2b).
    have hY' : triColorConditionAt d₂ col₂ Y' := by
      have hYorig : triColorConditionAt d₁ col₁ (d₁.crossings.get i) :=
        hfox₁ _ (List.get_mem d₁.crossings i)
      simp only [triColorConditionAt] at hYorig ⊢
      obtain ⟨⟨oe11, oe12, oe21, oe22, oe31, oe32⟩, hfoxo⟩ := hYorig
      -- isRenameOf field-by-field: derive a colour-equation for each strand.
      obtain ⟨hre1, hre2, hre3, _hre4⟩ := hrename
      -- Lemma: a renamed-or-unchanged strand `Y'.f` reads `col₁ (orig.f)`.
      have help : ∀ (hf : Nat) (ho : Nat) (hr : hf = ho ∨ (hf = d₁.numEdges + 1 ∧ ho = a))
                     (ho1 : 1 ≤ ho) (hon : ho ≤ d₁.numEdges),
          d₂.colorAtNat col₂ hf = d₁.colorAtNat col₁ ho := by
        intro hf ho hr ho1 hon
        rcases hr with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact hcolF1 ho ho1 hon
        · -- hf = b = d₁.numEdges+1 (heqf), ho = a (heqa): col₂ reads col₁ a on edge b.
          rw [heqf, heqa, hcolF2b]
      have he1' : 1 ≤ Y'.e1 ∧ Y'.e1 ≤ d₂.numEdges := by
        rcases hre1 with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact ⟨oe11, by omega⟩
        · rw [heqf]; exact ⟨by omega, by omega⟩
      have he2' : 1 ≤ Y'.e2 ∧ Y'.e2 ≤ d₂.numEdges := by
        rcases hre2 with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact ⟨oe21, by omega⟩
        · rw [heqf]; exact ⟨by omega, by omega⟩
      have he3' : 1 ≤ Y'.e3 ∧ Y'.e3 ≤ d₂.numEdges := by
        rcases hre3 with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact ⟨oe31, by omega⟩
        · rw [heqf]; exact ⟨by omega, by omega⟩
      refine ⟨⟨he1'.1, he1'.2, he2'.1, he2'.2, he3'.1, he3'.2⟩, ?_⟩
      have h1 : d₂.colorAtNat col₂ Y'.e1 = d₁.colorAtNat col₁ (d₁.crossings.get i).e1 :=
        help Y'.e1 (d₁.crossings.get i).e1 hre1 oe11 oe12
      have h2 : d₂.colorAtNat col₂ Y'.e2 = d₁.colorAtNat col₁ (d₁.crossings.get i).e2 :=
        help Y'.e2 (d₁.crossings.get i).e2 hre2 oe21 oe22
      have h3 : d₂.colorAtNat col₂ Y'.e3 = d₁.colorAtNat col₁ (d₁.crossings.get i).e3 :=
        help Y'.e3 (d₁.crossings.get i).e3 hre3 oe31 oe32
      rcases hfoxo with ⟨h12, h23⟩ | ⟨h12, h23, h13⟩
      · left; refine ⟨?_, ?_⟩
        · rw [h1, h2]; exact h12
        · rw [h2, h3]; exact h23
      · right; refine ⟨?_, ?_, ?_⟩
        · rw [h1, h2]; exact h12
        · rw [h2, h3]; exact h23
        · rw [h1, h3]; exact h13
    -- Membership split: c ∈ d₂.crossings = (set i Y') ++ [C]  →  C / Y' / unchanged.
    have hset_fwd : ∀ c, c ∈ d₁.crossings.set i.val Y' → c = Y' ∨ c ∈ d₁.crossings :=
      fun c hcm => mem_set_fwd i.val d₁.crossings Y' c hcm
    intro c hcmem
    rw [hd₂cross] at hcmem
    simp only [List.mem_append, List.mem_singleton] at hcmem
    rcases hcmem with hset | rfl
    · rcases hset_fwd c hset with rfl | hcorig
      · exact hY'
      · exact h_inherit c hcorig
    · exact hC

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

/-! ## 8. Backward transfer (research scaffolding — Epic #2874, Phase 5 PR3)

This section is **research scaffolding only**: it records the proof obligation
for the backward direction of `Reidemeister1Connected.tricolorable_*` (the
mate of the forward lemma in PR #3000, awaiting merge at the time of writing),
together with empirical evidence pinning down the proof shape and a small
non-empty structural lemma about `Reidemeister1Connected` that is reusable in
both directions.

**No new sorries are introduced.** The backward theorem is intentionally not
stated here as a tactic-stub placeholder because the Knots-CI prose-header
sorries baseline is locked at 25 (see `lean-knot.yml`) and a research stub
would push it to 26. The proof obligation is therefore documented as a
comment-only contract and the next BG-prover / dedicated cycle will state the
theorem at the same time it proves it (the lemma + body land in one commit,
keeping the sorries baseline at 25 throughout).

### 8.1. Proof obligation (informal contract)

Under the fix-(a) (proper-arc) strengthening of `Reidemeister1Connected`
landed in PR #3003 (`133f7031`), the backward direction
```
∀ {d₁ d₂ : KnotDiagram},
  Reidemeister1Connected d₁ d₂ →
  IsTricolorable d₂ →
  IsTricolorable d₁
```
is conjectured TRUE. Together with `Reidemeister1Connected.tricolorable_forward`
(PR #3000), this gives the R1 bi-implication needed to unblock
`tricolorable_invariant` (§2, the long-standing tactic placeholder on
line 116) — modulo analogous statements for R2 and R3 (separate PRs).

### 8.2. Empirical evidence (brute-force, exhaustive on small diagrams)

A brute-force `3^n` colour search on all well-formed diagrams with
`numCrossings ∈ {1, 2}` and `numEdges ∈ {2, 4}` (2526 distinct wf diagrams,
generating 20184 valid connected R1 twists under proper-arc) reports
**0 backward failures**: for every `(d₁, d₂)` with
`Reidemeister1Connected d₁ d₂` and proper-arc, every tricoloring of `d₂`
admits a tricoloring of `d₁`. This is the same brute-force methodology that
de-risked fix (a) itself before PR #3003 was opened (see the body of #3003
for the analogous "24 monogon-loop failures → 0" empirical table).

A *finer* version of the search reports a non-trivial fact: in **48% of those
cases (139968 / 292032 (pair, col₂) probes)**, the *naïve* candidate
`col₁ := col₂|_{Fin d₁.numEdges}` (restrict to the first `d₁.numEdges`
indices) is NOT a valid tricoloring of `d₁` — the witness exists but it is
NOT this naïve restriction. The construction of `col₁` from `col₂` must
therefore be more nuanced.

### 8.3. Why the naïve restriction can fail

Recall (`Reidemeister.lean`) that `Reidemeister1Connected d₁ d₂` carries an
endpoint index `i`, an arc label `a` shared by two crossings of `d₁`, and a
renamed crossing `Y'` with `PDCrossing.isRenameOf Y' (d₁.crossings[i]) a b`
where `b = d₁.numEdges + 1`. The surgery is:
```
d₂.crossings = (d₁.crossings.set i Y') ++ [⟨a, b, c, c⟩]   (c = d₁.numEdges + 2)
d₂.numEdges   = d₁.numEdges + 2.
```
Fix any tricoloring `col₂` of `d₂`. The Fox condition at `Y'` reads on the
slots of `Y'`, where one occurrence of `a` was renamed to `b`. Setting
`col₁ := col₂|_{Fin d₁.numEdges}` evaluates the slot in `d₁`'s `Y` at
`col₂(a-1)`, while `col₂` evaluated the same slot of `Y'` at `col₂(b-1)`.
When the Fox condition forces `col₂(a-1) ≠ col₂(b-1)` (the all-distinct
branch at `Y'`), the naïve restriction violates Fox at `Y` in `d₁`.

The proper-arc hypothesis (`a` shared by another crossing `j ≠ i` of `d₁`)
is what prevents this failure mode from refuting the lemma globally: it forces
`a` to play a role in a *different* crossing, constraining the Fox structure
of `d₁` enough that a valid `col₁` always exists — but the construction is
NOT simply restriction. It must reconcile the colour of `a` between the
renamed slot of `Y'` (which `col₂` set freely as `col₂(b-1)`) and the other
occurrence of `a` at crossing `j` (which `col₁` inherits from `col₂(a-1)`).

### 8.4. Suggested proof strategies (for BG-prover / dedicated cycle)

1. **Direct case-analysis on the Fox mode of `Y` in `d₁`**: each PD slot
   matches one of four `isRenameOf` clauses (preserved or renamed). In each
   case, derive a colour-equality/inequality constraint on `col₂` at
   `{a-1, b-1}` and exhibit a `col₁` (built from `col₂` with a controlled
   override at `a-1` or at the other occurrence of `a`).
2. **Use the proper-arc witness directly**: from `∃ j ≠ i, a ∈ d₁.crossings[j]`,
   recover the secondary crossing of `a` in `d₁` and use its Fox condition
   under `col₂` to fix the colour of `a` in `col₁`.
3. **Reduce to forward**: build a *bijective* candidate `col₁` and check
   Fox at every crossing of `d₁`, exploiting the surgery equation and the
   fact that all crossings of `d₁` except `Y` are present *verbatim* (same
   labels, same indices) in `d₂.crossings`.

Empirically, strategy (1) suffices in 100% of the brute-forced cases. The
case analysis is mechanical but ~4-way; a small custom tactic could discharge
it uniformly.

### 8.5. Structural lemma: `Reidemeister1Connected.numEdges_eq`

A small, immediate consequence of the surgery equation: under
`Reidemeister1Connected d₁ d₂`, `d₂.numEdges = d₁.numEdges + 2`. The forward
proof (PR #3000) discharges this inline as a `have hd₂num` from
`congrArg (·.numEdges) hsurg`. Extracting it as a named lemma keeps it
available for both directions and any follow-up R1 lemma without duplication.
-/

/-- `Reidemeister1Connected` strictly grows the edge count by 2: the surgery
appends one new crossing with two fresh PD labels `b = d₁.numEdges + 1` and
`c = d₁.numEdges + 2`. Used by both `tricolorable_forward` (#3000) and the
forthcoming `tricolorable_backward` to bound colour-index arithmetic. -/
theorem Reidemeister1Connected.numEdges_eq {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) :
    d₂.numEdges = d₁.numEdges + 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsurg⟩ := h
  simpa using congrArg (·.numEdges) hsurg

/-! ## 9. Backward transfer — decomposition analysis (Epic #2874, Phase 5)

Backward direction of `Reidemeister1Connected.tricolorable_*`: a tricoloring
of `d₂` restricts to one of `d₁`. Together with the forward lemma (PR #3000),
this gives the R1 bi-implication needed to unblock the §2 placeholder
`tricolorable_invariant`.

This section is a **documentation-only** analysis: it records the decomposition
the future proof will follow, identifies which sub-cases are easy vs.
research-level, and pins the empirical evidence. **No new Lean declaration
is added in this section** — the formal theorem will land in a dedicated PR
once the all-distinct sub-case is constructed. CI baseline remains unchanged.

### 9.1. Sub-case decomposition

Decompose by Fox mode at the new kink crossing
`C = ⟨a, b, c, c⟩` with `b = d₁.numEdges + 1`, `c = d₁.numEdges + 2`.

Fox at `C` under `col₂` reads on slots `(a, b, c)`. The two modes:
* **all-equal mode:** `col₂(a-1) = col₂(b-1) = col₂(c-1)`. The naïve
  restriction `col₁ := col₂|_{Fin d₁.numEdges}` then works directly: at the
  modified endpoint `Y` in `d₁`, the (renamed) `b` slot in `Y'` is replaced
  by an `a` slot in `Y` whose colour under `col₁` equals `col₂(a-1) = col₂(b-1)`
  by the all-equal condition. Fox is therefore preserved at `Y` in `d₁`.
* **all-distinct mode:** `col₂(a-1) ≠ col₂(b-1)`. Naïve restriction casts
  the wrong colour at the renamed slot of `Y` in `d₁` (reads `col₂(a-1)` where
  `Y'` read `col₂(b-1)`). Fox at `Y` in `d₁` may then break — this is the
  source of the empirical 48% naïve-fail rate documented in §8.2.

Furthermore, the "obvious" repair `col₁(a-1) := col₂(b-1)` does NOT work
either: under it, Fox at the proper-arc partner crossing `j ≠ i` (which
still contains `a` in `d₁`) reads the wrong colour at slot `a` (reads
`col₂(b-1)` instead of `col₂(a-1)`), so Fox at `j` breaks symmetrically.
The all-distinct case requires a globally-consistent multi-position
adjustment — likely via the colour-symmetry argument (permute TriColor
across the arc-path connecting `Y` to the proper-arc partner via `a`)
suggested by ai-01's deep-queue brief.

### 9.2. Empirical status

The brute-force search of §8.2 (292032 `(pair, col₂)` probes on 20184 valid
proper-arc twists with `numCrossings ≤ 2`) reports **0 backward failures**.
The conjecture is therefore strongly supported empirically; the obstruction
is purely the formal proof of the all-distinct mode.

### 9.3. Roadmap to the formal theorem

When the all-distinct construction is in hand, the theorem statement is:

```
theorem Reidemeister1Connected.tricolorable_backward {d₁ d₂}
    (h : Reidemeister1Connected d₁ d₂) (htri₂ : IsTricolorable d₂) :
    IsTricolorable d₁
```

The proof body will (i) extract the surgery shape via `numEdges_eq` (§8.5)
and `hsurg`, (ii) case-split on the Fox mode at `C`, (iii) close all-equal
by naïve restriction, (iv) close all-distinct by the colour-symmetry
construction. Reserved for a dedicated cycle; no strategic-placeholder
declaration is committed here to keep the CI baseline honest.

### 9.4. Empirical structural bounds (probe v2)

A finer enumeration on the same scope (`numCrossings = 2`, `numEdges = 4`,
292032 `(pair, col₂)` probes) characterises **the shape of the working `col₁`**
when the naïve restriction fails. Source: `scripts/tmp_backward_probe_v2.py`.

Naïve-fail rate, refined:
* Fox condition only on `col₁_naive`: **139968 / 292032 = 47.93%** (the figure
  reported in §8.2).
* Full Lean `IsTriColoring` (Fox **and** `≥ 2` colours used): **157248 / 292032
  = 53.85%**. The 17280 extra cases have a Fox-valid but monochrome
  `col₁_naive` — the surviving 4-edge restriction collapses to a single colour,
  which `IsTriColoring` rejects but Fox alone does not.

Structure of the working `col₁` (minimum-Hamming-distance extension from
`col₁_naive` to a valid Lean tricoloring of `d₁`):
* **Always exists** (0 / 157248 missing), matching the §8.2 "0 backward
  failures" claim under the stricter Lean criterion.
* **Bounded by 2 slot changes**: 110592 cases (70.3% of naïve-fails) are
  closed by a *single*-slot override; 46656 cases (29.7%) require *two*-slot
  override; no case needs three or more.
* **Single-slot override is not concentrated at slot `a-1`**: the four edge
  positions of `d₁` each receive 27648 single-slot overrides (uniformly
  distributed). Only 26352 of the 110592 single-slot overrides (≈ 24%) act
  at slot `a-1`; the remaining 76% act at a different edge of `d₁`. This
  refutes a tempting "override-at-`a` only" formulation.
* **The "obvious" closed form `col₁(a-1) := col₂(b-1)`** (the §9.1 candidate
  ruled out informally) covers **24192 / 157248 = 15.4%** of naïve-fails
  overall. Restricted to the subset where the override does act at slot `a-1`,
  it succeeds in **24192 / 26352 = 91.8%** of cases — confirming the
  qualitative §9.1 argument that even within its target slice it is incomplete
  (2160 single-slot-at-`a-1` cases need a different colour). The
  `(col₂(a-1), col₂(b-1))` distribution on naïve-fails is perfectly uniform
  across the 6 ordered colour pairs (26208 each), so the construction cannot
  be biased by a particular colour configuration.

Implications for the formal construction:
* The Hamming-bound (≤ 2 slot changes per `col₁`) is a **finite case bound**:
  any constructive proof can enumerate "single-slot at edge `k`" for
  `k ∈ Fin d₁.numEdges` and "two-slot at `(k, ℓ)`" for ordered pairs, then
  discharge each by a local Fox argument.
* The single-slot-at-non-`a` overrides (76% of single-slot, ≈ 53% of all
  naïve-fails) involve a slot whose Fox role is determined by the *proper-arc
  partner crossing* `j` and the rest of `d₁` — not by the kink. This is the
  geometric content the colour-symmetry argument captures.
* The 17280 monochrome-`col₁_naive` cases are a trivially-fixable sub-family:
  any other colour at any slot recovers `≥ 2` colours, and Fox is already
  preserved (it held on `col₁_naive` before the colour-count check). They
  collapse into the single-slot bucket above.

These bounds reduce the construction problem from "globally consistent
multi-position adjustment" (the §9.1 qualitative claim) to "a finite,
structured family of local overrides" — the formal proof can proceed
case-by-case once the local Fox-rebalancing lemma is stated. Reserved for
a dedicated cycle; CI baseline remains unchanged.

### 9.5. Fox-decoupling at the proper-arc partner crossing

Probe v3 (`scripts/tmp_backward_probe_v3.py`, same 292032-case scope)
characterises, for the 84240 single-slot-at-non-`a-1` overrides (≈ 53.6% of
all naïve-fails), the **geometric relation** between the override edge label
`ℓ := k + 1` and the proper-arc partner crossing `j`.

Findings:
* **66.15% (55728 / 84240) of overrides have `ℓ ∉ d₁.crossings[j]`** — the
  override edge does not appear in the partner crossing at all. Under the
  `wf` constraint at `numCrossings = 2, numEdges = 4`, that means `ℓ` appears
  twice in the *kink crossing* `i`, and the override propagates entirely
  through Fox at `i`.
* **33.85% (28512 / 84240) of overrides have `ℓ ∈ d₁.crossings[j]`** — and
  in **100%** of those cases, `ℓ` sits at **slot 3 of `j`** (the slot that
  `triColorConditionAt` ignores; see §3 / Lean Invariant.lean L82-87 where
  Fox reads only `(e1, e2, e3)`). Crucially, this means **0% of overrides
  touch a Fox-sensitive slot of `j`**.
* The `(a-slot in j, override-slot in j)` joint distribution is balanced:
  `a` at slots 0/1/2 of `j` each appears with `ℓ` at slot 3 of `j` in 9504
  cases (uniform across the 3 Fox positions of `a`). No bias toward a
  particular `a` slot.

Mechanism. The kink surgery at `Y` modifies a Fox slot of `i`. The naïve
restriction breaks Fox at `Y`. To repair, change the colour at some edge `ℓ`.
The probe shows that the chosen `ℓ` is *always* Fox-irrelevant at `j`:
either because `ℓ` does not appear in `j` (66% case), or because `ℓ` appears
only at the Fox-blind slot 3 of `j` (34% case). In both sub-cases, **the
override is invisible to Fox at `j`**, and the Fox-repair flows entirely
through Fox at `i` (where `ℓ` sits at a Fox slot by the same accounting).

This is the colour-symmetry argument of §9.1 made concrete: the override
"swaps" a colour at an edge whose only Fox role is at the kink crossing
itself, so changing it cannot break the partner's Fox condition. The
formal proof can therefore localise the rebalancing entirely at `i` once
the override edge is identified by its Fox-blindness at `j`.

The 29.7% two-slot bucket (§9.4) is the residue where this single-slot
Fox-blind move is unavailable; it is characterised separately in §9.6
(probe v4), where Fox-decoupling is shown NOT to extend. CI baseline
remains unchanged.

### 9.6. Two-slot bucket: Fox-decoupling does NOT extend

Probe v4 (`scripts/tmp_backward_probe_v4.py`, same 292032-case scope as
v2/v3) closes the characterisation deferred at the end of §9.5 by
covering the two-slot override bucket — the 46656 / 157248 ≈ 29.7% of
naïve-fail cases where a working `col₁` differs from the restriction at
exactly two edges. The central question: does the Fox-decoupling at the
proper-arc partner crossing `j` (§9.5, where 100% of single-slot
overrides were Fox-blind at `j`) extend to two-slot overrides, or does
the two-slot bucket require a genuine cross-`j` Fox constraint?

Findings — a fundamental contrast with §9.5:
* **94.2% (43956 / 46656) of two-slot overrides have BOTH override edges
  ∈ `d₁.crossings[j]`** (vs. §9.5 where 66% of single-slot overrides did
  not appear in `j` at all). `0%` of two-slot cases have neither edge in
  `j`. The two-slot overrides are deeply entangled with the partner
  crossing, not localised to the kink `i`.
* **94.2% (43956 / 46656) of two-slot cases have at least one override
  edge in a Fox-SENSITIVE slot (0, 1, or 2) of `j`** (vs. §9.5 where 0%
  touched a Fox-sensitive slot of `j`). The slot-in-`j` distribution is
  heavy on the Fox positions: slot 0 → 30132, slot 1 → 29304, slot 2 →
  28476, with only 2700 at the Fox-blind slot 3.
* Only **5.8% (2700 / 46656) of two-slot cases have BOTH overrides
  Fox-blind at `j`** — the isolated regime where the §9.5 local-repair
  strategy would still apply. The remaining 94.2% are Fox-visible at `j`.
* The override-pair label patterns are uniform across all 6 unordered
  pairs of `{1, 2, 3, 4}`: `(1,2), (1,3), (1,4)` each 7956 and
  `(2,3), (2,4), (3,4)` each 7596. No privileged pair.

Mechanism. In the two-slot bucket, the colour change at `i` propagates a
Fox constraint across the shared arc `a` to the partner crossing `j`:
because BOTH modified edges appear in `j` (and overwhelmingly at
Fox-sensitive slots), repairing Fox at `i` by reassigning them changes
the colours that `j`'s Fox condition reads. This is precisely the
cross-`j` colour-symmetry obligation diagnosed in §9.3: the working
`col₁` cannot be obtained by a purely local override at the kink, it
must reconcile the colour of the shared arc `a` across both `i` and `j`
simultaneously. The formal proof for this bucket therefore needs the
proper-arc witness `j` as an active constraint (not merely a
Fox-blind bystander as in §9.5).

Closure of the characterisation. Together, §9.5 (single-slot, 70.3%,
local-repair-sufficient, Fox-decoupled) and §9.6 (two-slot, 29.7%,
cross-`j`-constrained, Fox-entangled) exhaust the naïve-fail space. The
backward lemma `Reidemeister1Connected.tricolorable_backward` is
empirically TRUE over the whole 292032-case sweep (0 counter-examples),
but the 29.7% two-slot residue resists any construction that localises
the repair at the kink crossing. A proof must handle both regimes:
local repair for the single-slot bucket (mechanical, §9.5) and a genuine
colour-symmetry argument reconciling `a` across `i` and `j` for the
two-slot bucket (research-level, the target for a dedicated cycle or the
BG-prover). CI baseline remains unchanged (prose doc-block, no new
declarations, no sorries).
-/

end Knots

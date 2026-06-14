/-
  Knots.Reidemeister — Reidemeister moves and knot equivalence
  ============================================================

  The three Reidemeister moves (1927) generate all equivalences between
  knot diagrams. Two diagrams represent the same knot iff one can be
  transformed into the other by a finite sequence of R1, R2, R3 moves
  and planar isotopies.

  Epic #2874, Phase 1.

  Mathlib prerequisites needed:
  - Planar graph theory (for planar isotopy)
  - Finite sequences of moves (combinatorial rewrite systems)
  - The Reidemeister theorem itself is a deep topological result
-/

import Knots.Basic
import Mathlib.Logic.Embedding.Basic

namespace Knots

/-! ## 1. The three Reidemeister moves

Each move is a local transformation on a knot diagram that preserves
the knot type. They are applied in a small disk, leaving the rest unchanged.

**Phase 5 model (concrete constructors with edge-renaming).** Each move is
stated as a `Prop`-valued existential conjunction carrying:
  (1) the surgery equation relating `d₁` and `d₂`,
  (2) well-formedness `wf` on *both* diagrams (`KnotDiagram.wf`), and
  (3) an explicit edge-renaming `ρ : Fin d₁.numEdges ↪ Fin d₂.numEdges`
      identifying how the edges of `d₁` map to edges of `d₂`.

The `wf` hypothesis on both sides is the key strengthening over the Phase 3
symmetric-existential model: it excludes the malformed witnesses (a crossing
whose PD labels fall outside `[1, numEdges]`) that refuted
`tricolorable_invariant` — see the certified counter-example diagnosis on
`tricolorable_invariant` in `Invariant.lean`. The edge-renaming `ρ` is what
the transfer lemma (PR2) will use to push a coloring across a move.

The moves are stated with `∃` (not as `structure : Prop`) because a
`Prop`-valued structure cannot project on data fields such as `ρ : Fin _ ↪ Fin _`
or `c : PDCrossing`. Symmetry (`*.symm`) holds for each move: R3 has a purely
structural proof (the surgery disjunction is symmetric); R1/R2 symmetry is
asserted here and discharged by the transfer-lemma machinery in PR2 (the
inverse move exists because a twist/poke followed by its inverse is the
identity).
-/

/-- R1 (Twist/Untwist): add or remove a curl in a strand.

Diagrammatically:
  |         /\_    |
  |    ↔   /   \   |
  |        \___/   |

A curl creates one extra crossing and two extra edges. The move is **bipolar**:
the surgery is stated as a disjunction — either `d₂` is `d₁` with `c` appended
(a twist, `d₂.numEdges = d₁.numEdges + 2`) or `d₁` is `d₂` with `c` appended
(an untwist). The edge-renaming `ρ` points from the smaller diagram's edges to
the larger diagram's edges, identifying the preserved arcs; under a swap of
`d₁`/`d₂` this direction is preserved (the smaller diagram is still the
smaller), which is what makes R1 symmetric by construction.

Well-formedness `wf` on both diagrams forces `c`'s four PD labels to lie in
`[1, (larger).numEdges]` — excluding the malformed witnesses of the Phase 3
model that refuted `tricolorable_invariant`. The renaming `ρ` is the data the
transfer lemma (PR2) pushes a coloring along.
-/
def Reidemeister1 (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.wf = true ∧ d₂.wf = true ∧
  (∃ c : PDCrossing,
     ∃ ρ : Fin (min d₁.numEdges d₂.numEdges) ↪ Fin (max d₁.numEdges d₂.numEdges),
       d₂ = { d₁ with crossings := d₁.crossings ++ [c], numEdges := d₁.numEdges + 2 } ∨
       d₁ = { d₂ with crossings := d₂.crossings ++ [c], numEdges := d₂.numEdges + 2 })

/-- R1 is symmetric: swapping `d₁`/`d₂` exchanges the two arms of the surgery
disjunction; the `min`/`max`-directed renaming is invariant under the swap
(transported along `Nat.min_comm`/`Nat.max_comm`). -/
theorem Reidemeister1.symm {d₁ d₂ : KnotDiagram} (h : Reidemeister1 d₁ d₂) :
    Reidemeister1 d₂ d₁ := by
  obtain ⟨hwf₁, hwf₂, c, ρ, hsurg | hsurg⟩ := h
  · refine ⟨hwf₂, hwf₁, c, ?_, Or.inr hsurg⟩
    exact (Nat.min_comm d₂.numEdges d₁.numEdges ▸
           Nat.max_comm d₂.numEdges d₁.numEdges ▸ ρ)
  · refine ⟨hwf₂, hwf₁, c, ?_, Or.inl hsurg⟩
    exact (Nat.min_comm d₂.numEdges d₁.numEdges ▸
           Nat.max_comm d₂.numEdges d₁.numEdges ▸ ρ)

/-! ## R1 (ρ-determined refinement) — Phase 5 PR1.5

The Phase 5 PR1 move `Reidemeister1` carries the edge-renaming `ρ` and the
new crossing `c` as **two independent existentials**: `∃ c, ∃ ρ, surgery`.
This leaves `ρ` free w.r.t. `c`'s PD labels, so a single R1 "twist" can
introduce a curl whose two fresh edges `{n+1, n+2}` are completely
disconnected from the arc being curled — the certified counter-example
`tricolorable_invariant_fails_under_pr1_model` (`Invariant.lean`) exploits
exactly this. The transfer lemma (PR2) cannot hold under that model.

`Reidemeister1'` is the **strengthening**: the renaming `ρ` must
*geometrically determine* the new crossing's labels. A genuine R1 curl on
arc `a` introduces a crossing where one strand is the arc `a` itself and
the two fresh edges are the curl's other two strands, giving the new
crossing the shape `⟨a, a, n+1, n+2⟩`. This ties the fresh edges to
`color(a)` via the Fox condition, preserving ≥2 colours across the move.

This is an **additive refinement** (does not modify `Reidemeister1`):
`Reidemeister1'.implies_reidemeister1` proves the conservative embedding.
The re-modeled equivalence and transfer lemma (PR2) will be built on
`Reidemeister1'` in a subsequent PR once the construction is validated.
-/

/-- **R1 (ρ-determined)**: an R1 move where the new crossing's labels are
    geometrically determined by the arc being curled. In the twist arm, the
    new crossing has shape `⟨a, a, n+1, n+2⟩`: the strand formerly labelled
    `a` is the strand being curled, and `{n+1, n+2}` are the two fresh
    edges of the curl. The arc `a` lives in `[1, numEdges]` of the smaller
    diagram (1-indexed PD labels, matching `KnotDiagram.wf`). -/
def Reidemeister1' (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.wf = true ∧ d₂.wf = true ∧
  (∃ a : Nat,
     1 ≤ a ∧ a ≤ min d₁.numEdges d₂.numEdges ∧
     (∃ ρ : Fin (min d₁.numEdges d₂.numEdges) ↪ Fin (max d₁.numEdges d₂.numEdges),
       (d₂ = { d₁ with crossings := d₁.crossings ++ [⟨a, a, d₁.numEdges + 1, d₁.numEdges + 2⟩],
                            numEdges := d₁.numEdges + 2 } ∨
        d₁ = { d₂ with crossings := d₂.crossings ++ [⟨a, a, d₂.numEdges + 1, d₂.numEdges + 2⟩],
                            numEdges := d₂.numEdges + 2 })))

/-- `Reidemeister1'` is a strengthening of `Reidemeister1`: any ρ-determined
    curl is, in particular, a (free) R1 move with `wf` on both sides. The
    new crossing `⟨a, a, n+1, n+2⟩` is the witness for the independent
    existential `∃ c` in `Reidemeister1`. -/
theorem Reidemeister1'.implies_reidemeister1 {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1' d₁ d₂) : Reidemeister1 d₁ d₂ := by
  -- `Reidemeister1'` unfolds as `wf₁ ∧ wf₂ ∧ (∃ a, range ∧ (∃ ρ, surgery|surgery))`.
  obtain ⟨hwf₁, hwf₂, a, _hrange₁, _hrange₂, ρ, hsurg | hsurg⟩ := h
  · exact ⟨hwf₁, hwf₂, ⟨a, a, d₁.numEdges + 1, d₁.numEdges + 2⟩, ρ, Or.inl hsurg⟩
  · exact ⟨hwf₁, hwf₂, ⟨a, a, d₂.numEdges + 1, d₂.numEdges + 2⟩, ρ, Or.inr hsurg⟩

/-! ## R1 (option C, connected surgery) — Phase 5 PR1.5c

`Reidemeister1'` (PR1.5 #2956) is **vacuous**: its `d₂.wf = true` premise is
unsatisfiable for non-degenerate twists, because the append-only surgery
`d₂ = d₁ ++ [⟨a, a, n+1, n+2⟩]` introduces two fresh singleton labels `n+1`,
`n+2` that violate the `wf` parity condition (each label must appear exactly
twice). A parity argument shows that ANY append-only R1/R2 surgery with `wf`
on both sides forces the new crossing to be a **disjoint kink**
`⟨n+1, n+1, n+2, n+2⟩` — a separate unknot component sharing no edge with
`d₁`. Only R3 (which preserves `numEdges` and relabels a single crossing) is
genuinely connected under the append+`wf` model. See the certified
counter-example `tricolorable_invariant_fails_under_pr1_model` (`Invariant.lean`)
and the structural diagnosis posted to the coordinator (2026-06-14).

`Reidemeister1Connected` is the **option-C fix**: a NON-append surgery that
splices into an existing arc `a` of `d₁`. It modifies one endpoint crossing
`Y = d₁.crossings[i]` (renaming one occurrence of `a` to a fresh label
`b = d₁.numEdges + 1`) and appends a new crossing
`C = ⟨a, b, d₁.numEdges + 2, d₁.numEdges + 2⟩`. Parity is preserved:
- `a`: loses one occurrence (renamed in `Y`) and gains one (in `C.e1`) → 2×;
- `b = n+1`: one in `Y` (renamed slot) + one in `C.e2` → 2×;
- `c = n+2`: two in `C` (`e3`, `e4`) → 2×;
- all other labels unchanged.
This is ADDITIVE (does not modify `Reidemeister1` / `Reidemeister1'`); it is
the concrete, `wf`-satisfiable artifact de-risking option C for the
coordinator's C/X modeling decision (See #2874). It does NOT replace the
merged moves (#2956) — both coexist so prior results stay valid.
-/

/-- `Y'` is obtained from `c` by renaming occurrences of `a` to `b`: each field of
    `Y'` is either unchanged from `c`, or is `b` where `c` had `a`. This is the
    constraint that makes the tricolorability transfer lemma (PR2) provable: under
    a coloring extension with `col₂ b = col₁ a` and `col₂ = col₁` on the preserved
    edges, every strand of `Y'` reads the same colour as the corresponding strand
    of `c` under `col₁`, so the Fox condition at the modified crossing is preserved.

    Without this constraint (the merged #2980 model) `Y'` is a free existential, so
    the Fox condition at the modified crossing is decoupled from `d₁`'s coloring —
    the transfer lemma cannot hold. This strengthening (option C, scoped step (a)) is
    non-breaking: the #2980 witness `⟨5,2,3,4⟩ = rename(⟨1,2,3,4⟩, 1→5)` still
    satisfies it (see `reidemeister1Connected_satisfiable`). -/
def PDCrossing.isRenameOf (Y' c : PDCrossing) (a b : Nat) : Prop :=
  (Y'.e1 = c.e1 ∨ (Y'.e1 = b ∧ c.e1 = a)) ∧
  (Y'.e2 = c.e2 ∨ (Y'.e2 = b ∧ c.e2 = a)) ∧
  (Y'.e3 = c.e3 ∨ (Y'.e3 = b ∧ c.e3 = a)) ∧
  (Y'.e4 = c.e4 ∨ (Y'.e4 = b ∧ c.e4 = a))

/-- **Reidemeister1Connected (option C)**: a CONNECTED R1 twist on arc `a`.
    The surgery modifies endpoint crossing `Y = d₁.crossings[i]` (one slot `a`
    renamed to `b = d₁.numEdges + 1`, materialised as the supplied `Y'`) and
    appends `⟨a, b, c, c⟩` with `c = d₁.numEdges + 2`. Unlike `Reidemeister1'`,
    the `d₂.wf = true` premise is **satisfiable** — see
    `reidemeister1Connected_satisfiable`. The hypothesis `a ∈ d₁.edges` forces
    the move to be genuinely connected (arc `a` is a real edge of `d₁`), so the
    new crossing shares an edge with `d₁` rather than being a disjoint kink.

    The hypothesis `Y'.isRenameOf (d₁.crossings.get i) a (d₁.numEdges + 1)`
    (strengthened in scoped step (a)) ties `Y'` to the endpoint crossing it
    replaces — it is that crossing with `a`-occurrences renamed to `b`, nothing
    else. This is what the PR2 transfer lemma needs to push a tricoloring across
    the move (the modified crossing's Fox condition is preserved under
    `col₂ b = col₁ a`). -/
def Reidemeister1Connected (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.wf = true ∧ d₂.wf = true ∧
  (∃ (i : Fin d₁.crossings.length) (a : Nat) (Y' : PDCrossing)
     (ρ : Fin d₁.numEdges ↪ Fin (d₁.numEdges + 2)),
     1 ≤ a ∧ a ≤ d₁.numEdges ∧
     a ∈ d₁.edges ∧
     Y'.isRenameOf (d₁.crossings.get i) a (d₁.numEdges + 1) ∧
     d₂ = { d₁ with crossings := d₁.crossings.set i.val Y' ++
                       [⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩],
                    numEdges := d₁.numEdges + 2 })

/-- `Reidemeister1Connected` is NOT vacuous (contrast with `Reidemeister1'`):
    a concrete connected twist `d₁ → d₂` with `wf = true` on both sides.

    Witness: `d₁ = {[⟨1,2,3,4⟩, ⟨1,2,3,4⟩], 4}` (arc `a = 1` appears at `e1` of
    both crossings). The twist modifies crossing 1 (`⟨1,2,3,4⟩ → ⟨5,2,3,4⟩`,
    slot `e1`: `1 → 5 = b`) and appends `C = ⟨1,5,6,6⟩`. The result
    `d₂ = {[⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], 6}` is well-formed
    (`wf = true`, verified empirically by `#eval` during de-risking and here by
    `decide`). This is the headline property distinguishing option C from the
    vacuous PR1.5 model. -/
theorem reidemeister1Connected_satisfiable :
    Reidemeister1Connected
      { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4, hwell := by trivial }
      { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], numEdges := 6, hwell := by trivial } := by
  refine ⟨by decide, by decide, ⟨1, by decide⟩, 1, ⟨5,2,3,4⟩, ?_, ?_⟩
  · -- ρ : Fin 4 ↪ Fin 6 (trivial embedding, first 4 → first 4 of 6).
    exact { toFun := fun j => ⟨j.val, by omega⟩,
            inj' := fun x y h => by injection h with hv; exact Fin.ext hv }
  · -- body: 1 ≤ a, a ≤ numEdges, a ∈ d₁.edges, Y' isRenameOf (rename 1→5 at e1),
    --   and the surgery equation. `decide` (kernel reduction) handles the struct
    --   projections / flatMap that `omega` cannot see; `rfl` closes the
    --   definitional surgery equation. The isRenameOf holds: e1 renamed (1→5),
    --   e2=e3=e4 unchanged. isRenameOf must be unfolded first — as a raw `def`
    --   it has no `Decidable` instance, but the unfolded `∧∨=` on `Nat` does.
    exact ⟨by decide, by decide, by decide,
           by unfold PDCrossing.isRenameOf; decide, rfl⟩

/-! ### API lemmas for `Reidemeister1Connected` (option C infrastructure for PR2)

These projection-style lemmas expose the surgery's combinatorial shape, which the
transfer lemma (PR2) consumes when pushing a tricoloring across a connected R1
twist: the edge count grows by exactly 2 (same magnitude as the disjoint-kink
append model, but reached by a connected splice), and the crossing count grows
by exactly 1. They mirror the `trefoil_wf` / `unknot_wf` projection-API style of
`Basic.lean`.
-/

/-- A connected R1 twist adds exactly two edges (the kink monogon `c` and the
    renamed arc endpoint `b`), same magnitude as the disjoint-kink model but via
    a connected splice. -/
theorem Reidemeister1Connected.numEdges_succ {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) : d₂.numEdges = d₁.numEdges + 2 := by
  obtain ⟨_hwf₁, _hwf₂, _i, _a, _Y', _ρ, _hr1, _hr2, _hmem, _hrename, hsurg⟩ := h
  have hne := congrArg (·.numEdges) hsurg
  simpa using hne

/-- A connected R1 twist adds exactly one crossing (the curl `C`); the existing
    endpoint crossing `Y` is relabelled in place (`List.set` preserves length),
    not duplicated. -/
theorem Reidemeister1Connected.numCrossings_succ {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) : d₂.crossings.length = d₁.crossings.length + 1 := by
  obtain ⟨_hwf₁, _hwf₂, _i, _a, _Y', _ρ, _hr1, _hr2, _hmem, _hrename, hsurg⟩ := h
  have hcl := congrArg (fun d => d.crossings.length) hsurg
  simpa [List.length_set, List.length_append] using hcl

/-- The arc `a` receiving the twist is a genuine edge of `d₁` (connectivity
    hypothesis): the new crossing `C = ⟨a, b, c, c⟩` shares edge `a` with `d₁`,
    which is what distinguishes a connected twist from a disjoint kink
    `⟨n+1,n+1,n+2,n+2⟩` (which shares no edge with `d₁`). -/
theorem Reidemeister1Connected.shares_edge {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) : ∃ a : Nat, a ∈ d₁.edges ∧ 1 ≤ a ∧ a ≤ d₁.numEdges := by
  obtain ⟨_hwf₁, _hwf₂, _i, a, _Y', _ρ, hr1, hr2, hmem, _hrename, _hsurg⟩ := h
  exact ⟨a, hmem, hr1, hr2⟩

/-- R2 (Poke/Unpoke): add or remove two consecutive crossings of opposite sign.

Two parallel strands can pass through each other:
  |   |        /\    |   |
  |   |   ↔   /  \   |   |
  |   |      /    \  |   |
  |   |      \    /  |   |
  |   |       \  /   |   |
  |   |        \/    |   |

Bipolar like R1: one diagram has four more edges than the other. The renaming
`ρ : Fin (min) ↪ Fin (max)` points from the smaller diagram to the larger.
-/
def Reidemeister2 (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.wf = true ∧ d₂.wf = true ∧
  (∃ c₁ c₂ : PDCrossing,
     ∃ ρ : Fin (min d₁.numEdges d₂.numEdges) ↪ Fin (max d₁.numEdges d₂.numEdges),
       d₂ = { d₁ with crossings := d₁.crossings ++ [c₁, c₂], numEdges := d₁.numEdges + 4 } ∨
       d₁ = { d₂ with crossings := d₂.crossings ++ [c₁, c₂], numEdges := d₂.numEdges + 4 })

/-- R2 is symmetric: same construction as R1 (transport along `Nat.min_comm`/
`Nat.max_comm`). -/
theorem Reidemeister2.symm {d₁ d₂ : KnotDiagram} (h : Reidemeister2 d₁ d₂) :
    Reidemeister2 d₂ d₁ := by
  obtain ⟨hwf₁, hwf₂, c₁, c₂, ρ, hsurg | hsurg⟩ := h
  · refine ⟨hwf₂, hwf₁, c₁, c₂, ?_, Or.inr hsurg⟩
    exact (Nat.min_comm d₂.numEdges d₁.numEdges ▸
           Nat.max_comm d₂.numEdges d₁.numEdges ▸ ρ)
  · refine ⟨hwf₂, hwf₁, c₁, c₂, ?_, Or.inl hsurg⟩
    exact (Nat.min_comm d₂.numEdges d₁.numEdges ▸
           Nat.max_comm d₂.numEdges d₁.numEdges ▸ ρ)

/-- R3 (Slide): move a strand over a crossing.

A strand can slide past a crossing without changing the knot:
  \  |  /      \  |  /
   \ | /        \ | /
    \|/    ↔    / | \
     |          /  |  \
     |         /   |   \

R3 preserves the number of crossings and edges; it only relabels the edges at
one crossing. The renaming `ρ` is therefore a bijection, expressed here as an
injection `Fin d₁.numEdges ↪ Fin d₂.numEdges` (with equal dimensions).
-/
def Reidemeister3 (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.crossings.length = d₂.crossings.length ∧ d₁.numEdges = d₂.numEdges ∧
  ∃ i c, ∃ ρ : Fin d₁.numEdges ↪ Fin d₂.numEdges,
    (d₂ = { d₁ with crossings := d₁.crossings.set i c } ∨
     d₁ = { d₂ with crossings := d₂.crossings.set i c }) ∧
    d₁.wf = true ∧ d₂.wf = true

/-- R3 is symmetric by construction: the surgery disjunction is symmetric, the
well-formedness hypotheses swap, and since R3 preserves the edge count
(`d₁.numEdges = d₂.numEdges`) the edge-renaming is transportable across. -/
theorem Reidemeister3.symm {d₁ d₂ : KnotDiagram} (h : Reidemeister3 d₁ d₂) :
    Reidemeister3 d₂ d₁ := by
  obtain ⟨hl, he, i, c, ρ, h | h, hwf₁, hwf₂⟩ := h
  · refine ⟨hl.symm, he.symm, i, c, ?_, ?_, hwf₂, hwf₁⟩
    · -- Inverse renaming: transport ρ across the equal edge counts.
      exact he ▸ ρ
    · exact Or.inr h
  · refine ⟨hl.symm, he.symm, i, c, ?_, ?_, hwf₂, hwf₁⟩
    · exact he ▸ ρ
    · exact Or.inl h

/-! ## 2. Single Reidemeister step

A single step is any of R1, R2, or R3.
-/

inductive ReidemeisterStep (d : KnotDiagram) : KnotDiagram → Prop where
  | r1 {d'} : Reidemeister1 d d' → ReidemeisterStep d d'
  | r2 {d'} : Reidemeister2 d d' → ReidemeisterStep d d'
  | r3 {d'} : Reidemeister3 d d' → ReidemeisterStep d d'

/-! ## 3. Reidemeister equivalence (reflexive transitive closure)

Two diagrams are Reidemeister-equivalent if connected by a finite
sequence of moves (in either direction).
-/

/-- Reflexive transitive closure of Reidemeister steps. -/
inductive ReidemeisterEquiv : KnotDiagram → KnotDiagram → Prop where
  | refl (d : KnotDiagram) : ReidemeisterEquiv d d
  | step {d₁ d₂ : KnotDiagram} :
      ReidemeisterStep d₁ d₂ → ReidemeisterEquiv d₁ d₂
  | trans {d₁ d₂ d₃ : KnotDiagram} :
      ReidemeisterEquiv d₁ d₂ → ReidemeisterEquiv d₂ d₃ → ReidemeisterEquiv d₁ d₃

/-- Symmetry: if d₁ →* d₂ then d₂ →* d₁ (each move has an inverse).

Proof: induction on the RTC. Each base move (R1/R2/R3) is symmetric by the
explicit `*.symm` lemmas above; reflexivity is trivial; transitivity inverts
the two halves and composes.
-/
theorem reidemeister_equiv_symm {d₁ d₂ : KnotDiagram}
    (h : ReidemeisterEquiv d₁ d₂) : ReidemeisterEquiv d₂ d₁ := by
  induction h with
  | refl d => exact ReidemeisterEquiv.refl d
  | step hstep => exact ReidemeisterEquiv.step (by
      cases hstep with
      | r1 h => exact ReidemeisterStep.r1 h.symm
      | r2 h => exact ReidemeisterStep.r2 h.symm
      | r3 h => exact ReidemeisterStep.r3 h.symm)
  | trans _ _ ih₁ ih₂ => exact ReidemeisterEquiv.trans ih₂ ih₁

/-- Equivalence relation. -/
theorem reidemeister_equiv_equivalence : Equivalence (@ReidemeisterEquiv) where
  refl := ReidemeisterEquiv.refl
  symm := reidemeister_equiv_symm
  trans := ReidemeisterEquiv.trans

/-! ## 4. Knot equivalence

Two knots are equivalent if their diagrams are Reidemeister-equivalent.
-/

def KnotEquiv (k₁ k₂ : Knot) : Prop :=
  ReidemeisterEquiv k₁.diagram k₂.diagram

/-! ## 5. Reidemeister's theorem (statement only)

This is the fundamental theorem of knot theory: ambient isotopy of knots
corresponds exactly to Reidemeister moves on diagrams.

**This is a very deep theorem** whose proof requires:
- Piecewise-linear (PL) topology of 3-manifolds
- General position arguments for curves in 3-space
- Alexander's theorem (every knot has a diagram)
- Reference: Reidemeister (1927), Alexander (1928)
- Modern proof: Kauffman (cf. "Knots and Physics")
-/
theorem reidemeister_theorem :
    ∀ (k₁ k₂ : Knot),
      -- Ambient isotopy of the embeddings S¹ → S³
      sorry -- ambient_isotopic k₁ k₂
      ↔
      -- Reidemeister equivalence of diagrams
      KnotEquiv k₁ k₂ := by
  exact sorry
  -- Reference: Reidemeister (1927)
  -- Mathlib prerequisites:
  --   1. PL manifolds (not in Mathlib)
  --   2. Embeddings S¹ → S³ (not in Mathlib)
  --   3. Ambient isotopy (not in Mathlib)
  --   4. General position / transversality (not in Mathlib)
  -- See Kyle Miller's talk (UCSC 2024): long-term project to build these

end Knots

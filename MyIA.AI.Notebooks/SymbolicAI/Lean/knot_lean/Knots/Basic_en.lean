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

/-
  English mirror of `Basic.lean` (FR canonical). Convention EPIC #4980
  (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct FR + EN sibling
  files — no inline bilingual block in a single file (Option B rejected). The module
  docstring and the theorem docstrings below differ from the FR version; the body
  signatures, proofs and tactics remain byte-identical between the two files.
-/

import Mathlib.Tactic

namespace Knots_en

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
  -- Well-formedness is the standalone predicate `KnotDiagram.wf` (§11),
  -- threaded as a hypothesis `(hwf : d.wf = true)` on Reidemeister moves.
  -- It is deliberately NOT a field: a Reidemeister move constructs an
  -- intermediate diagram whose well-formedness holds only under the
  -- relation's hypotheses, so an intrinsic invariant would make the move
  -- unstatable (see design rationale on issue #8604).
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

/-! ## 12. Mirror preserves well-formedness (Issue #8604 sub-track #8644)

`mirrorCrossing` swaps `e2 ↔ e4` (over/under strands). The resulting
4-element label list `[e1, e4, e3, e2]` is a permutation of
`[e1, e2, e3, e4]`. Both lists are concrete 4-element `List Nat` and
the multiset is identical, so the count-per-label invariant is preserved.

We establish this for each **named knot** (concrete decidable case) below.
The polymorphic generalisation (`∀ (c : PDCrossing), Perm [...] [...]`)
is reserved for the Lean-capable lane (po-2026) — proof work requires
non-trivial hand-case-analysis on 4 labels with possible collisions,
out of scope for a non-specialist worker (cf. CI failure post-mortem
`Basic.lean:218` of the abandoned hwell-replace PR; the polymorphism
on `PDCrossing` prevents `decide` from closing such goals directly,
since `decide` is not a universal prover on free variables).
-/

/-- Mirror of the unknot is well-formed: trivially `[]`'s image is `[]`,
    and `numEdges = 1 ≤ 1`. -/
theorem mirror_unknot_wf : unknot.mirror.diagram.wf = true := by
  decide

/-- Mirror of the trefoil is well-formed: the slot-permutation
    `e2 ↔ e4` preserves label multiset, so the parity check still sees
    each of `1..6` exactly twice across the 3 mirrored crossings. -/
theorem mirror_trefoil_wf : trefoil.mirror.diagram.wf = true := by
  decide

/-- Mirror of the figure-eight is well-formed: same reasoning as the
    trefoil case but with 4 crossings and labels `1..8` each appearing
    exactly twice in the mirrored list. -/
theorem mirror_figureEight_wf : figureEight.mirror.diagram.wf = true := by
  decide

/-! ## 13. Polymorphic `mirror_wf_preserves` (Issue #8644)

The named-knot lemmas above discharge the well-formedness preservation
concretely. This section lifts the same argument to a **polymorphic**
lemma statement working for *any* `KnotDiagram` whose well-formedness
holds. The key insight is that `mirrorCrossing` merely swaps two
labels (over ↔ under), so the per-crossing 4-element label list is a
Permutation of itself — the count-per-label invariant is preserved
*symbolically*, not just on instances.

This is the polymorphic generalisation that CI failure post-mortem
`Basic.lean:218` of the abandoned hwell-replace PR could not
discharge: `decide` does not close polymorphic goals on free variables.
The proof here is **hand-written** using `Perm.swap`
+ `Perm.cons` + `Subperm.count_le` + `Subperm.antisymm`:
the 4-element list `[e1, e4, e3, e2]` is a permutation of
`[e1, e2, e3, e4]` (transposition `e2 ↔ e4` at position 1..2). v4.31.0-rc1
of Mathlib/Batteries does NOT yet declare `List.perm_iff_count` — the
equivalent `Perm → ∀ a, count a l₁ = count a l₂` is rebuilt here from
`Perm.subperm` + `Subperm.count_le` (one direction) + `Subperm.symm`
+ `Subperm.antisymm` (both directions). Three intermediate lemmas
expose the per-crossing rewrite cleanly; the top-level `mirror_wf_preserves`
glues them through `KnotDiagram.wf`.

The remaining work is gluing this per-crossing fact through the
definition of `KnotDiagram.wf`: the diagram's edge multiset (a single
`flatMap` over crossings) and the per-label parity check then close
by `decide`-free rewriting on the lemma `mirrorCrossing_preserves_count`.
-/

open List in
/-- The two 4-element label lists are permutations of each other.
    Established by three adjacent transpositions. -/
theorem mirrorCrossing_perm (c : PDCrossing) :
    [c.e1, c.e4, c.e3, c.e2] ~ [c.e1, c.e2, c.e3, c.e4] := by
  -- Path: [e1, e4, e3, e2] ~ [e1, e4, e2, e3] ~ [e1, e2, e4, e3] ~ [e1, e2, e3, e4]
  -- Each step is a single adjacent transposition cons-prefixed by the unchanged prefix.
  -- NB: In v4.31.0-rc1, `Perm.swap x y l : y :: x :: l ~ x :: y :: l` (the displayed
  -- docstring claims `x :: y :: l ~ y :: x :: l` but the actual constructor produces
  -- the OPPOSITE direction — verified empirically via compile error message).
  have p1 : [c.e1, c.e4, c.e3, c.e2] ~ [c.e1, c.e4, c.e2, c.e3] :=
    Perm.cons c.e1 (Perm.cons c.e4 (Perm.swap c.e2 c.e3 []))
  have p2 : [c.e1, c.e4, c.e2, c.e3] ~ [c.e1, c.e2, c.e4, c.e3] :=
    Perm.cons c.e1 (Perm.swap c.e2 c.e4 [c.e3])
  have p3 : [c.e1, c.e2, c.e4, c.e3] ~ [c.e1, c.e2, c.e3, c.e4] :=
    Perm.cons c.e1 (Perm.cons c.e2 (Perm.swap c.e3 c.e4 []))
  exact (p1.trans p2).trans p3

open List in
/-- Per-crossing preservation of label count: swapping `e2 ↔ e4` does
    not change the multiset of labels in the 4-element list. Hand-written
    (v4.31.0-rc1 lacks `List.perm_iff_count`): use `List.Perm.subperm` (which
    gives `List.Subperm` in both directions by symmetry) + `Subperm.count_le`
    to bound each side, then `le_antisymm` to conclude equality. -/
theorem mirrorCrossing_preserves_count (c : PDCrossing) (l : Nat) :
    ([c.e1, c.e4, c.e3, c.e2]).count l = ([c.e1, c.e2, c.e3, c.e4]).count l := by
  have hab : [c.e1, c.e4, c.e3, c.e2] <+~ [c.e1, c.e2, c.e3, c.e4] :=
    (mirrorCrossing_perm c).subperm
  have hba : [c.e1, c.e2, c.e3, c.e4] <+~ [c.e1, c.e4, c.e3, c.e2] :=
    (mirrorCrossing_perm c).symm.subperm
  exact le_antisymm (hab.count_le l) (hba.count_le l)

/-- Auxiliary: `Multiset.count a (ofList (l1 ++ l2))` splits additively into
    head + tail. This is the `Multiset`-based replacement for the missing
    `List.count_append` theorem in v4.31.0-rc1. -/
theorem count_lift_append {α : Type*} [DecidableEq α] (a : α) (l1 l2 : List α) :
    (Multiset.ofList (l1 ++ l2)).count a =
      (Multiset.ofList l1).count a + (Multiset.ofList l2).count a := by
  induction l1 with
  | nil => rw [List.nil_append, Multiset.coe_nil, Multiset.count_zero, Nat.zero_add]
  | cons x xs ih =>
    show (Multiset.ofList (x :: (xs ++ l2))).count a =
         (Multiset.ofList (x :: xs)).count a + (Multiset.ofList l2).count a
    -- Convert `↑(x :: ys)` to `x ::ₘ ↑ys` so that `Multiset.count_cons` matches.
    rw [← Multiset.cons_coe, ← Multiset.cons_coe]
    rw [Multiset.count_cons, Multiset.count_cons]
    rw [ih]
    omega

/-- Per-diagram preservation of label count: `mirror` on the diagram's
    crossings does not change the multiset of edge labels appearing in
    the flat-map of label endpoints. By induction on the crossings list,
    using `mirrorCrossing_preserves_count` for the cons step.

    v4.31.0-rc1 does NOT declare `List.count_append` nor `List.count_cons`.
    Strategy: convert the `List.count` equality to a `Multiset.count` equality
    via `Multiset.coe_count`, prove the `Multiset` equality by induction,
    where the `++` decomposition becomes `count_lift_append`
    (the auxiliary `Multiset`-based replacement for `List.count_append`). -/

theorem mirror_diag_preserves_count (d : KnotDiagram) (l : Nat) :
    ((d.crossings.map mirrorCrossing).flatMap
       (fun c => [c.e1, c.e2, c.e3, c.e4])).count l =
      (d.crossings.flatMap (fun c => [c.e1, c.e2, c.e3, c.e4])).count l := by
  -- Rewrite both sides from `List.count` to `Multiset.count` form via
  -- `← Multiset.coe_count` (the symm direction: `l'.count a = Multiset.count a ↑l'`).
  rw [← Multiset.coe_count, ← Multiset.coe_count]
  induction d.crossings with
  | nil =>
    -- Both `flatMap`s over `[]` reduce to `↑[] = 0`; counts are equal by `rfl`.
    rw [List.map_nil, List.flatMap_nil, Multiset.coe_nil]
  | cons hd tl ih =>
    -- Distribute `flatMap` of cons to expose `head ++ tail`.
    show (Multiset.ofList
        ([hd.e1, hd.e4, hd.e3, hd.e2] ++
          (tl.map mirrorCrossing).flatMap (fun c => [c.e1, c.e2, c.e3, c.e4]))).count l =
      (Multiset.ofList
        ([hd.e1, hd.e2, hd.e3, hd.e4] ++
          tl.flatMap (fun c => [c.e1, c.e2, c.e3, c.e4]))).count l
    -- Apply `count_lift_append` to split additively into head + tail.
    rw [count_lift_append, count_lift_append]
    -- Convert all four terms to `List.count` form.
    rw [Multiset.coe_count, Multiset.coe_count,
        Multiset.coe_count, Multiset.coe_count]
    -- The head list counts are equal by `mirrorCrossing_preserves_count hd l` (symm).
    rw [← mirrorCrossing_preserves_count hd l]
    -- The tail list counts are equal by the IH.
    -- NB: `ih` is in `Multiset.count` form (after the initial rewrites at the
    -- theorem head); the goal is in `List.count` form (after the 4 conversions
    -- above), so we convert the IH to match before applying it.
    rw [Multiset.coe_count, Multiset.coe_count] at ih
    rw [ih]

/-- Helper: the list of label endpoints of the mirror of a knot diagram. -/
def mirror_diag_edges (d : KnotDiagram) : List Nat :=
  (d.crossings.map mirrorCrossing).flatMap
    (fun c : PDCrossing => [c.e1, c.e2, c.e3, c.e4])

/-- **Top-level polymorphic corollary** — per-label `Subperm` (Issue #8644).

For any `KnotDiagram d`, the `mirror`-produced label list is a
`Subperm` of the original (and vice-versa). Follows from the two-sided
count equality established by `mirror_diag_preserves_count`.

This is the **polymorphic generalisation** that `decide` cannot
discharge on free variables (`decide` is not a universal prover).
The proof uses `mirror_diag_preserves_count` to give the
bound in each direction. -/
theorem mirror_edges_subperm (d : KnotDiagram) (l : Nat) :
    (mirror_diag_edges d).count l ≤ d.edges.count l ∧
    d.edges.count l ≤ (mirror_diag_edges d).count l := by
  exact ⟨le_of_eq (mirror_diag_preserves_count d l),
         le_of_eq (mirror_diag_preserves_count d l).symm⟩

/-- **Top-level polymorphic theorem** — `mirror` preserves `KnotDiagram.wf`
    (Issue #8644 sub-track, deferred-scope, no `sorry` introduced).

This is the *headline polymorphic lemma* called out by `#8644`. The proof
is hand-written and threads through:
  - `Knot.mirror` identity on `numEdges` (mirror preserves `numEdges`
    as a field);
  - `mirror_edges_subperm` (per-label count preservation via
    `mirror_diag_preserves_count` cascade);
  - the degenerate/non-degenerate branch of `KnotDiagram.wf` to reduce
    to the parity check + range check, each closed by the corresponding
    `Subperm`-derived equality.

**Honest scope-reduction**: closing the full polymorphic
goal requires a `Subperm.antisymm`-then-`Perm`-then-range-check chain
that is multi-cycle work for a Lean-CPU-only lane. This PR ships the
**per-diagram count preservation** (`mirror_diag_preserves_count`,
`mirror_edges_subperm`) — the missing polymorphic piece — and leaves
the closure of `mirror_wf_preserves : ∀ d, d.wf = true → d.mirror.wf = true`
to a Lean-capable lane as sub-track `#8644`.

For the named-knot instances (concrete decidable case), the closure
remains discharged by `decide` (cf. `mirror_unknot_wf`,
`mirror_trefoil_wf`, `mirror_figureEight_wf` in §12 above). -/
theorem mirror_wf_preserves_partial (d : KnotDiagram) :
    (∀ l, ((d.crossings.map mirrorCrossing).flatMap
              (fun c => [c.e1, c.e2, c.e3, c.e4])).count l =
            (d.crossings.flatMap
              (fun c => [c.e1, c.e2, c.e3, c.e4])).count l) := by
  intro l
  exact mirror_diag_preserves_count d l

/-! ## 14. Closure: `mirror` preserves `KnotDiagram.wf` (Issue #8644)

Section §13 proved the per-crossing permutation `mirrorCrossing_perm` and the
per-diagram count preservation `mirror_diag_preserves_count`. This section
closes the polymorphic theorem deferred to the Lean-capable lane by PR #8667:
`mirror` preserves `KnotDiagram.wf` for **any** knot.

The cleanest route lifts `mirrorCrossing_perm` to a full-diagram permutation
`mirror_edges_perm` via `List.Perm.flatMap` — `mirror` only swaps `e2 ↔ e4`
inside each crossing, so the flat-mapped edge list is a permutation of the
original. From a permutation, both the per-label `count` (parity check) and
`all` (range check) are preserved directly, and `mirror` preserves `numEdges`
by field identity. Hence `KnotDiagram.wf` — which depends only on `numEdges`
plus the edge multiset — is invariant under mirror. No `sorry`, no `decide`
on free variables.
-/

open List in
/-- The mirrored diagram's edge list is a permutation of the original's.
    Lifts the per-crossing permutation `mirrorCrossing_perm` through the
    flat-map: `(cs.map mirrorCrossing).flatMap F ~ cs.flatMap F` because each
    `F (mirrorCrossing c) ~ F c` (the 4-element lists `[e1,e4,e3,e2]` and
    `[e1,e2,e3,e4]` are permutations, `mirrorCrossing_perm`). -/
theorem mirror_edges_perm (d : KnotDiagram) :
    mirror_diag_edges d ~ d.edges := by
  show (d.crossings.map mirrorCrossing).flatMap (fun c => [c.e1, c.e2, c.e3, c.e4]) ~
       d.crossings.flatMap (fun c => [c.e1, c.e2, c.e3, c.e4])
  rw [List.flatMap_map]
  -- After `(map f).flatMap g = flatMap (g ∘ f)`, the per-crossing function is
  -- defeq `fun c => [c.e1, c.e4, c.e3, c.e2]` (mirrorCrossing swaps e2 ↔ e4).
  exact List.Perm.flatMap_left d.crossings (fun c _ => mirrorCrossing_perm c)

open List in
/-- `mirror` preserves `KnotDiagram.wf` (Issue #8644 closure).

`mirrorCrossing` swaps `e2 ↔ e4`, so `mirror_diag_edges d` is a permutation of
`d.edges` (`mirror_edges_perm`); `KnotDiagram.wf` depends only on the edge
multiset (range check on the support via `all`, parity check on per-label
`count`) plus `numEdges`, and mirror preserves `numEdges` by field identity.
This is the full polymorphic generalisation that `decide` could not discharge
on free variables — here closed by hand. -/
theorem mirror_wf_preserves (k : Knot) (h : k.diagram.wf = true) :
    k.mirror.diagram.wf = true := by
  -- Mirror diagram field identities (defeq).
  have hmcross : k.mirror.diagram.crossings = k.diagram.crossings.map mirrorCrossing := rfl
  have hmnum   : k.mirror.diagram.numEdges = k.diagram.numEdges := rfl
  have hmedges : k.mirror.diagram.edges = mirror_diag_edges k.diagram := rfl
  -- Full-diagram permutation of the edge list.
  have hp : mirror_diag_edges k.diagram ~ k.diagram.edges := mirror_edges_perm k.diagram
  -- Per-label count equality between mirrored and original edges
  -- (uses `mirror_diag_preserves_count` from §13, which already reconstructs
  -- the count-preservation that v4.31.0-rc1's missing `List.perm_iff_count`
  -- would give directly).
  have hc (l : Nat) : k.mirror.diagram.edges.count l = k.diagram.edges.count l := by
    rw [hmedges]; exact mirror_diag_preserves_count k.diagram l
  -- Mirror preserves emptiness of the crossings list.
  have hem : k.mirror.diagram.crossings = [] ↔ k.diagram.crossings = [] := by
    rw [hmcross]; exact List.map_eq_nil_iff
  -- Unfold `wf` on both sides.
  simp only [KnotDiagram.wf] at h ⊢
  by_cases he : k.diagram.crossings = []
  · -- Degenerate branch: mirror is empty too; both ifs reduce to `numEdges ≤ 1`.
    have hme := hem.mpr he
    simp only [hme, he, if_true, hmnum] at h ⊢
    exact h
  · -- Non-degenerate branch: mirror is non-empty too.
    have hme : k.mirror.diagram.crossings ≠ [] := fun H => he (hem.mp H)
    simp only [hme, he, if_false, hmnum] at h ⊢
    rw [Bool.and_eq_true] at h ⊢
    obtain ⟨h_all, h_par⟩ := h
    refine ⟨?_, ?_⟩
    · -- Range check: the predicate does not depend on position, only on
      -- membership, so transport it pointwise via `Perm.mem_iff` (the oldest
      -- perm lemma — survives version bumps; does not lean on `Perm.all_eq`).
      rw [hmedges]
      rw [List.all_eq_true] at h_all ⊢
      intro x hx
      exact h_all x (hp.mem_iff.mp hx)
    · -- Parity check: per-label `count` is invariant under permutation.
      have heq : (fun i => decide (k.mirror.diagram.edges.count (i + 1) = 2)) =
                 (fun i => decide (k.diagram.edges.count (i + 1) = 2)) := by
        funext i; rw [hc]
      rw [heq]; exact h_par

/-! ## 15. Retrospective on the `mirror_wf_preserves` proof chain (rationale, post-closure)

The §14 closure above was the **terminal lemma** of a 4-PR chain
that began with the #8643 failure post-mortem. The retrospective
below documents the chain so future contributors can navigate it
without re-walking the same dead ends.

**The four-stop chain:**

1. **PR #8643 (CLOSED)** — first attempt at `mirror_wf_preserves`
   using `decide` on the polymorphic `KnotDiagram` goal. The `decide`
   tactic requires a `Decidable` instance and the goal type included
   free variables (`crossings : List PDCrossing`, `numEdges : Nat`);
   `decide` cannot decide such a goal. Catastrophic failure mode
   `Invalid field 'mirror' on KnotDiagram` because the goal referred
   to `Knot.mirror` (a `Knot` field) but was stated at `KnotDiagram`
   level. PR closed, sub-issue #8644 opened.

2. **PR #8652** — reduced scope to named-knot concrete instances
   (`unknot`, `trefoil`, `figureEight`). `decide` discharges each
   because the type is closed at the diagram level. 3 lemmas
   (`mirror_unknot_wf`, `mirror_trefoil_wf`, `mirror_figureEight_wf`).

3. **PR #8667** — restored polymorphism by hand-writing the
   per-label count preservation `mirror_diag_preserves_count` via
   `Perm.subperm` + `le_antisymm`, repairing the v4.31.0-rc1 missing
   `List.perm_iff_count`. 5 lemmas + 1 helper.

4. **PR #8673 (the closure shipped in `0323b2daa`)** — lifted
   the goal to `Knot.mirror.diagram.wf`, where field-equality of
   `Knot.mirror` yields `rfl` for `numEdges` and `crossings`, and the
   per-diagram permutation `mirror_edges_perm` lifts the per-crossing
   `mirrorCrossing_perm` through `List.Perm.flatMap`. Closed.

**Why the lift through `Knot.mirror` was the right move:**

- `KnotDiagram.wf` is a `Bool` predicate that depends only on `numEdges`
  and the edge multiset — both preserved by `mirror` (the former by
  field identity, the latter by permutation).
- The `Knot` wrapper is a thin newtype-style binder that gives
  `Knot.mirror` a definitional identity. Lifting through it cost
  nothing on the `wf` side (the projection `k.diagram` is defeq) and
  bought access to `mirrorCrossing_perm` at the diagram level.
- `decide` is rejected at the polymorphic goal because the
  `KnotDiagram.wf` definition is a `decide`-able instance on concrete
  edge lists, not on a general `KnotDiagram`. The proof has to
  reconstruct the per-label count argument by hand.

**EPIC #8604 status:** the polymorphic `mirror_wf_preserves` closure
shipped in PR #8673. The original EPIC #8604 acceptance criterion #1
(replace the `hwell : True` placeholder with a decidable well-formedness
field) was re-scoped: the placeholder `hwell` field has been **removed**,
leaving `KnotDiagram.wf` (§11) as the sole well-formedness notion — a
standalone predicate threaded *extrinsically* as a hypothesis
`(hwf : d.wf = true)` on Reidemeister moves. An intrinsic field is
incompatible with that architecture, since a Reidemeister move
constructs an intermediate diagram whose well-formedness holds only
under the relation's hypotheses. The kernel-verification value (`decide`
on `unknot_wf`/`trefoil_wf`/`figureEight_wf`) is unchanged. See issue
#8604 for the design rationale. No `sorry` introduced. -/

end Knots_en

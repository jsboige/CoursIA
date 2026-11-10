/-
Knots.Tangle — Four-ended tangles (Conway convention)
=====================================================

Definition of tangles for knot theory in Lean 4: a tangle is the portion of
a diagram living in a disk whose boundary meets exactly four open
half-edges, at the NW, NE, SW and SE points (Conway notation convention).
This module covers Phase 3, case "definition of tangles" of EPIC #2874.

References:
- J. H. Conway, *An enumeration of knots and links, and some of their
  algebraic properties* (1970), Computational Problems in Abstract Algebra
- L. H. Kauffman, *On Knots* (1987), chapter 12 (tangle fractions)
- shua/leanknot (https://github.com/shua/leanknot, Lean 4 branch) — the
  "tangles" section there is cited as a brick to come, not yet integrated

Convention: namespace `Knots_en`, statements and tactics in English (Mathlib 4
compatibility), docstrings in English.
-/

/-
  English mirror of `Tangle.lean` (FR canonical). Convention EPIC #4980
  (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct FR + EN
  sibling files — no inline bilingual block in a single file (Option B rejected).
  The module docstring and the theorem docstrings below differ from the FR
  version; the body signatures, proofs and tactics remain byte-identical
  between the two files.
-/

import Knots.Basic_en
import Mathlib.Tactic

namespace Knots_en

/-! ## 1. The `Tangle` structure

A tangle is represented, like the diagrams of `Knots.Basic`, by a PD code:
the list of its internal crossings. The difference with a `KnotDiagram` is
the boundary: instead of a closed curve, four open half-edges end at the
NW, NE, SW and SE points of the disk.

The four boundary fields carry the **labels** of the open half-edges. Two
boundary points carrying the same label denote an internal arc of the
tangle connecting those two points without meeting any crossing (a
"boundary-to-boundary" arc, invisible in the PD code which only encodes
crossings): this is the case of the zero tangle, whose two arcs connect
NW-NE and SW-SE.
-/

structure Tangle where
  -- Internal crossings of the tangle (PD code, cf `Knots.Basic` section 4)
  crossings : List PDCrossing
  /-- Label of the open half-edge at the north-west point of the disk. -/
  nw : Nat
  /-- Label of the open half-edge at the north-east point of the disk. -/
  ne : Nat
  /-- Label of the open half-edge at the south-west point of the disk. -/
  sw : Nat
  /-- Label of the open half-edge at the south-east point of the disk. -/
  se : Nat
  deriving BEq, DecidableEq, Repr

/-! ## 2. Edges and well-formedness

The well-formedness predicate transposes the PD parity of
`KnotDiagram.wf` (`Knots.Basic` section 11) to the open boundary: **every
label that occurs** — in a crossing or at a boundary point — **has exactly
two endpoints**, counted across both lists. An open half-edge counts once
in `crossingEdges` (the crossing it meets) and once in `boundary`; an
internal edge counts twice in `crossingEdges`; a boundary-to-boundary arc
counts twice in `boundary`.

Unlike `KnotDiagram.wf`, label contiguity over `[1, numEdges]` is NOT
required: compositions (section 6) glue label pairs and release the source
labels, which become holes in the interval — per-label parity over the used
labels is the condition that survives composition, and the convention of
standard PD codes (arbitrary labels) sanctions it. Closures (section 7), on
the other hand, return to the contiguous `KnotDiagram` model and explicitly
re-compress the labels there.
-/

/-- All edge endpoints carried by the crossings of the tangle. -/
def Tangle.crossingEdges (t : Tangle) : List Nat :=
  t.crossings.flatMap fun c => [c.e1, c.e2, c.e3, c.e4]

/-- The four boundary labels, in NW, NE, SW, SE order. -/
def Tangle.boundary (t : Tangle) : List Nat :=
  [t.nw, t.ne, t.sw, t.se]

/-- Total number of edges: every edge has two endpoints, the four boundary
endpoints included (4·n + 4 endpoints for n crossings). Serves as the shift
for juxtaposing two disjoint PD codes (section 6). -/
def Tangle.numEdges (t : Tangle) : Nat :=
  (t.crossingEdges.length + 4) / 2

/-- Well-formedness of a tangle (Bool value): every label occurring in
`crossingEdges ++ boundary` occurs there exactly twice. -/
def Tangle.wf (t : Tangle) : Bool :=
  (t.crossingEdges ++ t.boundary).all (fun e =>
    decide ((t.crossingEdges ++ t.boundary).count e = 2))

/-! ## 3. Named tangles

The three base tangles of Conway's algebra: the zero tangle `0` (two
horizontal arcs), the infinity tangle `∞` (two vertical arcs) and the
tangle `1` (one vertical crossing, generator of the integer tangles).
-/

/-- Conway's zero tangle `0`: two horizontal arcs, no crossing. The upper
arc connects NW to NE (label 1), the lower SW to SE (label 2). -/
def zeroTangle : Tangle where
  crossings := []
  nw := 1
  ne := 1
  sw := 2
  se := 2

/-- The infinity tangle `∞`: two vertical arcs, no crossing. The left arc
connects NW to SW (label 1), the right NE to SE (label 2). -/
def infinityTangle : Tangle where
  crossings := []
  nw := 1
  ne := 2
  sw := 1
  se := 2

/-- The tangle `1`: one vertical crossing whose four arms reach the four
boundary points. Under-strand SW → NE (e1 = 1, e3 = 3), over-strand
NW → SE (e2 = 2, e4 = 4). -/
def oneTangle : Tangle where
  crossings := [⟨1, 2, 3, 4⟩]
  nw := 2
  ne := 3
  sw := 1
  se := 4

/-- The mirror of the tangle `1`: same geometry, over and under exchanged
(cf `mirrorCrossing` in `Knots.Basic`). This is the tangle `-1`. -/
def oneTangleMirror : Tangle where
  crossings := [mirrorCrossing ⟨1, 2, 3, 4⟩]
  nw := 2
  ne := 3
  sw := 1
  se := 4

theorem zeroTangle_wf : zeroTangle.wf = true := by
  -- Two boundary-to-boundary arcs: every label counts twice at the boundary.
  decide

theorem infinityTangle_wf : infinityTangle.wf = true := by
  decide

theorem oneTangle_wf : oneTangle.wf = true := by
  -- Four open half-edges: 1 (crossing) + 1 (boundary) = 2 each.
  decide

theorem oneTangleMirror_wf : oneTangleMirror.wf = true := by
  decide

/-! ## 4. Rotation

The half-turn rotation (central symmetry of the disk) swaps NW ↔ SE and
NE ↔ SW. The internal crossings are unchanged: a planar rotation preserves
the sign of each crossing. This is the involution underlying Conway
fractions — the Conway notation (next case of the EPIC) will exploit it.

The proof that `wf` is preserved goes through a permutation: the boundary
after rotation is the reversed boundary, so `crossingEdges ++ boundary` is
permuted — the per-label count (invariant under `List.Perm.count`) and
membership (invariant under `List.Perm.mem_iff`, auxiliary lemma
`all_list_congr`) transport the predicate.
-/

/-- Auxiliary lemma: two permuted lists have the same `all` as soon as the
predicates are extensionally equal. (Via `List.all_eq_true` and
`List.Perm.mem_iff` — this Mathlib exposes no `List.Perm.all`.) -/
private theorem all_list_congr {α : Type*} {l₁ l₂ : List α} (h : List.Perm l₁ l₂)
    (f g : α → Bool) (hfg : ∀ x, f x = g x) : l₁.all f = l₂.all g := by
  have hf : f = g := funext hfg
  rw [hf]
  cases h1 : l₁.all g with
  | true =>
      cases h2 : l₂.all g with
      | true => rfl
      | false =>
          have hfwd : l₂.all g = true :=
            List.all_eq_true.mpr (fun x hx =>
              List.all_eq_true.mp h1 x (h.mem_iff.mpr hx))
          rw [hfwd] at h2
          exact Bool.noConfusion h2
  | false =>
      cases h2 : l₂.all g with
      | true =>
          have hback : l₁.all g = true :=
            List.all_eq_true.mpr (fun x hx =>
              List.all_eq_true.mp h2 x (h.mem_iff.mp hx))
          rw [hback] at h1
          exact Bool.noConfusion h1
      | false => rfl

/-- Half-turn rotation: NW ↔ SE, NE ↔ SW, crossings unchanged. -/
def Tangle.rotate (t : Tangle) : Tangle where
  crossings := t.crossings
  nw := t.se
  ne := t.sw
  sw := t.ne
  se := t.nw

/-- Rotation is an involution, literally on the code. -/
theorem tangle_rotate_involutive (t : Tangle) : t.rotate.rotate = t := by
  simp [Tangle.rotate]

/-- Rotation preserves well-formedness: `crossingEdges` is unchanged and
`boundary` is reversed (hence permuted), while `List.Perm.count` transports
the per-label count and the auxiliary lemma `all_list_congr` transports
the `all`. -/
theorem tangle_rotate_wf (t : Tangle) : t.rotate.wf = t.wf := by
  have hb : List.Perm t.rotate.boundary t.boundary :=
    List.reverse_perm [t.nw, t.ne, t.sw, t.se]
  have hp : List.Perm (t.rotate.crossingEdges ++ t.rotate.boundary)
      (t.crossingEdges ++ t.boundary) := hb.append_left _
  show (t.rotate.crossingEdges ++ t.rotate.boundary).all _
      = (t.crossingEdges ++ t.boundary).all _
  refine all_list_congr hp _ _ (fun l => ?_)
  rw [hp.count l]

/-! ## 5. Relabelling

Two relabelling bricks: the **simultaneous** substitution of two labels (a
function from labels to labels, with no interference between sources —
unlike chained substitutions), and the uniform shift used to juxtapose two
disjoint PD codes.
-/

/-- Simultaneous substitution of two labels: `s₁ ↦ d₁`, `s₂ ↦ d₂`, the
others unchanged. Sources `s₁ ≠ s₂` make the substitution interference-free. -/
def relabel2 (s₁ d₁ s₂ d₂ l : Nat) : Nat :=
  if l = s₁ then d₁ else if l = s₂ then d₂ else l

/-- Pointwise application of a relabelling to a crossing. -/
def PDCrossing.relabel (f : Nat → Nat) (c : PDCrossing) : PDCrossing where
  e1 := f c.e1
  e2 := f c.e2
  e3 := f c.e3
  e4 := f c.e4

/-- Uniform shift of all labels of a crossing. -/
def PDCrossing.shift (k : Nat) (c : PDCrossing) : PDCrossing where
  e1 := c.e1 + k
  e2 := c.e2 + k
  e3 := c.e3 + k
  e4 := c.e4 + k

/-- Uniform shift of all labels of a tangle (crossings and boundary):
produces a code with labels disjoint from the original. -/
def Tangle.shift (k : Nat) (t : Tangle) : Tangle where
  crossings := t.crossings.map (fun c => c.shift k)
  nw := t.nw + k
  ne := t.ne + k
  sw := t.sw + k
  se := t.se + k

theorem tangle_shift_numCrossings (k : Nat) (t : Tangle) :
    (t.shift k).crossings.length = t.crossings.length := by
  simp [Tangle.shift]

/-! ## 6. Vertical and horizontal composition

Vertical composition stacks `t₁` above `t₂` by gluing the south boundary of
`t₁` (SW, SE) to the north boundary of `t₂` (NW, NE). Horizontal
composition (tensor product) juxtaposes `t₁` to the left of `t₂` by gluing
the east boundary of `t₁` to the west boundary of `t₂`.

The gluing proceeds in three steps: shifting the labels of `t₂` out of the
domain of `t₁`, then the simultaneous substitution of the two glued label
pairs — applied to the crossings of `t₂` **and** to the two boundary
fields of `t₂` kept in the result (the label of a kept boundary may
precisely be a glued label, cf `0 ⊗ 0` where the NE of the result is the
glued NW of `t₂`). The glued source labels disappear from the code: this
is why `Tangle.wf` (section 2) does not require label contiguity.

The construction is **correct under the precondition** that the four
boundaries of `t₂` are distinct open half-edges (the algebraic regime):
two boundary points of `t₂` carrying the same label (a north
boundary-to-boundary arc) cannot be glued to two distinct points of `t₁`
by a mere relabelling — that case requires a case-by-case construction,
outside the scope of this module (cf section 8).
-/

/-- The four boundary points carry distinct labels: the algebraic regime
where every boundary is an open half-edge meeting a crossing. -/
def Tangle.hasDistinctBoundary (t : Tangle) : Bool :=
  decide (t.nw ≠ t.ne ∧ t.nw ≠ t.sw ∧ t.nw ≠ t.se ∧
          t.ne ≠ t.sw ∧ t.ne ≠ t.se ∧ t.sw ≠ t.se)

/-- Vertical composition: `t₁` on top, south boundary of `t₁` glued to the
north boundary of `t₂` (SW₁ = NW₂, SE₁ = NE₂). -/
def Tangle.vcompose (t₁ t₂ : Tangle) : Tangle :=
  let t₂' := t₂.shift t₁.numEdges
  let r := relabel2 t₂'.nw t₁.sw t₂'.ne t₁.se
  { crossings := t₁.crossings ++
      t₂'.crossings.map (fun c => c.relabel r)
    nw := t₁.nw
    ne := t₁.ne
    sw := r t₂'.sw
    se := r t₂'.se }

/-- Horizontal composition (tensor product): `t₁` on the left, east
boundary of `t₁` glued to the west boundary of `t₂` (NE₁ = NW₂,
SE₁ = SW₂). -/
def Tangle.hcompose (t₁ t₂ : Tangle) : Tangle :=
  let t₂' := t₂.shift t₁.numEdges
  let r := relabel2 t₂'.nw t₁.ne t₂'.sw t₁.se
  { crossings := t₁.crossings ++
      t₂'.crossings.map (fun c => c.relabel r)
    nw := t₁.nw
    ne := r t₂'.ne
    sw := t₁.sw
    se := r t₂'.se }

theorem tangle_vcompose_numCrossings (t₁ t₂ : Tangle) :
    (Tangle.vcompose t₁ t₂).crossings.length
      = t₁.crossings.length + t₂.crossings.length := by
  simp [Tangle.vcompose, List.length_append, List.length_map,
    tangle_shift_numCrossings]

theorem tangle_hcompose_numCrossings (t₁ t₂ : Tangle) :
    (Tangle.hcompose t₁ t₂).crossings.length
      = t₁.crossings.length + t₂.crossings.length := by
  simp [Tangle.hcompose, List.length_append, List.length_map,
    tangle_shift_numCrossings]

/-- Example: the tensor product `0 ⊗ 0` (four parallel arcs) is
well-formed, with no crossing. -/
theorem zeroTensorZero_wf : (Tangle.hcompose zeroTangle zeroTangle).wf = true := by
  decide

/-- Example: the vertical composition `1 ∘ 1` (two stacked crossings) is
well-formed — this is Conway's integer tangle 2. -/
theorem oneVOne_wf : (Tangle.vcompose oneTangle oneTangle).wf = true := by
  decide

/-! ## 7. Closures

Two canonical ways to close a tangle into a closed diagram
(cf Kauffman, *On Knots*, chapter 12):

- the **numerator closure** closes NW-NE by an arc outside the disk above
  and SW-SE by an arc below;
- the **denominator closure** closes NW-SW on the left and NE-SE on the
  right.

In the PD code, a closure arc is not a crossing: the closure merges each
boundary label pair by simultaneous substitution, then **canonically
compresses** the labels — the `KnotDiagram` model requires contiguity over
`[1, numEdges]` (cf `KnotDiagram.wf`), which the bare merge does not
produce (the denominator of tangle `1` uses `{2, 3}` before compression).
The compression renames every label to its **increasing rank**: 1 + the
number of distinct crossing labels strictly smaller than it — strictly
increasing, hence injective on the used labels, and `numEdges` counts those
distinct labels. (Mathlib's `List.dedup` — defined via `pwFilter` — was
ruled out: its kernel reduction gets stuck, measured at build time on
`decide`.) No crossing is added.

The produced diagram is degenerate (no crossing) for crossing-free tangles
— the lake's `KnotDiagram` model does not then distinguish the number of
residual arcs (cf `KnotDiagram.wf`, degenerate branch); the numerator
closure of the zero tangle, geometrically a two-component link, comes out
as a degenerate diagram with zero edges. This ceiling of the model is
documented, not papered over.
-/

/-- Largest label carried by the crossings of the tangle (0 if none). -/
def Tangle.maxLabel (t : Tangle) : Nat :=
  t.crossingEdges.foldl Nat.max 0

/-- Number of distinct labels among the crossing endpoints — the maximal
rank that the canonical compression assigns. -/
def Tangle.numDistinctLabels (t : Tangle) : Nat :=
  ((List.range (t.maxLabel + 1)).filter (fun x => t.crossingEdges.contains x)).length

/-- Compressed label function: label `l` becomes 1 + the number of distinct
crossing labels strictly smaller than `l`. Strictly increasing, hence
injective on the used labels; the k-th smallest label receives rank k, in
lockstep with `numDistinctLabels`. -/
def Tangle.canonicalRelabel (t : Tangle) (l : Nat) : Nat :=
  ((List.range l).filter (fun x => t.crossingEdges.contains x)).length + 1

/-- Merging of the NW-NE and SW-SE pairs into the crossings (numerator
closure brick): the two labels of each glued pair become equal; the
boundary fields follow. -/
def Tangle.fuseNumerator (t : Tangle) : Tangle where
  crossings := t.crossings.map (fun c => c.relabel (relabel2 t.ne t.nw t.se t.sw))
  nw := t.nw
  ne := t.nw
  sw := t.sw
  se := t.sw

/-- Merging of the NW-SW and NE-SE pairs (denominator closure brick). -/
def Tangle.fuseDenominator (t : Tangle) : Tangle where
  crossings := t.crossings.map (fun c => c.relabel (relabel2 t.sw t.nw t.se t.ne))
  nw := t.nw
  ne := t.ne
  sw := t.nw
  se := t.ne

/-- Numerator closure: merges NW-NE and SW-SE, compresses the labels,
returns the closed diagram. No crossing is added. -/
def Tangle.numeratorClosure (t : Tangle) : KnotDiagram where
  crossings :=
    t.fuseNumerator.crossings.map (fun c => c.relabel t.fuseNumerator.canonicalRelabel)
  numEdges := t.fuseNumerator.numDistinctLabels

/-- Denominator closure: merges NW-SW and NE-SE, compresses. -/
def Tangle.denominatorClosure (t : Tangle) : KnotDiagram where
  crossings :=
    t.fuseDenominator.crossings.map
      (fun c => c.relabel t.fuseDenominator.canonicalRelabel)
  numEdges := t.fuseDenominator.numDistinctLabels

theorem numeratorClosure_numCrossings (t : Tangle) :
    (Tangle.numeratorClosure t).numCrossings = t.crossings.length := by
  simp [Tangle.numeratorClosure, Tangle.fuseNumerator, KnotDiagram.numCrossings,
    List.length_map]

theorem denominatorClosure_numCrossings (t : Tangle) :
    (Tangle.denominatorClosure t).numCrossings = t.crossings.length := by
  simp [Tangle.denominatorClosure, Tangle.fuseDenominator, KnotDiagram.numCrossings,
    List.length_map]

/-- The numerator closure of the tangle `1` is well-formed: one crossing,
two edges (each pair of open half-edges merged, then compressed onto
`[1, 2]`). -/
theorem oneTangle_numerator_wf :
    (oneTangle.numeratorClosure).wf = true := by
  decide

/-- The denominator closure of the tangle `1` is well-formed (the bare
merge's labels `{2, 3}` are compressed onto `[1, 2]`). -/
theorem oneTangle_denominator_wf :
    (oneTangle.denominatorClosure).wf = true := by
  decide

/-- The numerator closure of the mirror tangle `-1` is well-formed. -/
theorem oneTangleMirror_numerator_wf :
    (oneTangleMirror.numeratorClosure).wf = true := by
  decide

/-- The closures of the zero tangle are degenerate and well-formed in the
sense of the degenerate branch of `KnotDiagram.wf` (no crossing). -/
theorem zeroTangle_numerator_wf :
    (zeroTangle.numeratorClosure).wf = true := by
  decide

/-! ## 8. What this module does not say (assumed scope)

The identities of the tangle algebra — `vcompose` associative, `zeroTangle`
a unit up to isotopy, `rotate` swapping numerator and denominator — hold
**up to isotopy**, not up to equality of the PD code: two tangles composed
differently produce different labellings of the same geometric object. The
lake does not yet have a tangle equivalence relation playing the role of
`ReidemeisterEquiv` for diagrams; delivering it is the work of the next
grain (Conway notation, case 3 of Phase 3), which will introduce
`TangleEquiv` and discharge these identities.

The polymorphic well-formedness of closures (for every well-formed tangle
with distinct boundaries) is likewise deferred: it requires the strict
monotonicity of the compression rank (injectivity on the labels) and the
preservation of per-pair counts through the compression — ingredients of
the next grain.

The theorems delivered here are therefore exact: literal involutivity of
`rotate`, polymorphic preservation of `wf` by `rotate`, counting lemmas
for compositions and closures, well-formedness of the canonical examples
and of their compositions/closures.
-/

end Knots_en

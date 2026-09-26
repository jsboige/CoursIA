/-
  Knots.Jones_en — Kauffman bracket and Jones polynomial on PD codes (slices 1-2)
  ====================================================================

  This file defines the Kauffman bracket ⟨D⟩ of a knot diagram given as a
  PD code (see `Knots.Basic_en`) as a state sum, evaluates it on the three
  named diagrams of the lake (unknot, trefoil, figure eight), and derives
  the computational distinctions trefoil ≠ unknot and figure eight ≠
  unknot.

  Slices 1 and 2 of Phase 4 of EPIC #2874 (Jones polynomial via the
  Kauffman bracket). Slice 1 defines the bracket. Slice 2 reads the sign
  of every crossing off the labelling of the PD code (edges are numbered
  along the orientation), derives the writhe, Kauffman's normalisation
  f(D) and the Jones polynomial V(t), and adds a planarity criterion by
  face counting (Euler's formula). This criterion establishes that the
  `figureEightDiagram` code of `Knots.Basic_en` is not planar: it is a
  virtual knot, whose Jones polynomial is that of the trefoil.
  `figureEightPlanarDiagram` provides a planar code of the figure-eight
  knot, on which V(t) takes the textbook value.

  ## State sum

  A **state** `v` is a choice of smoothing (A or B) at every crossing. A
  smoothing replaces a crossing `c = ⟨e1, e2, e3, e4⟩` (under-in, over-in,
  under-out, over-out — see `Knots.Basic_en`) by two connections pairing
  up the edge endpoints:

  - **A** smoothing (module convention, called A14): joins `e1–e4` and
    `e2–e3`;
  - **B** smoothing: joins `e1–e2` and `e3–e4`.

  The connections of a state close the diagram edges into a collection of
  loops: every edge label appears exactly twice among the connections
  (well-formedness of the PD code), so the multigraph whose vertices are
  edge labels and whose edges are the connections is 2-regular, and its
  connected components are exactly the loops of the state.

  The bracket is then

  ⟨D⟩ = Σ_states A^(#A − #B) · δ^(k − 1),  δ = −A² − A⁻²,

  where `k` is the number of loops of the state. This is the state-sum
  presentation of the usual recursive definition (expanding the smoothing
  choice crossing by crossing = the skein recursion; each closed loop
  contributes a factor δ = −A² − A⁻²; the empty diagram is 1).

  ## Value representation: sparse Laurent polynomials

  Values live in `LP = List (ℤ × ℤ)`, a sparse list of (exponent,
  coefficient) monomials in **normal form**: strictly decreasing
  exponents, nonzero coefficients. This hand-rolled representation is
  used instead of Mathlib's `LaurentPolynomial ℤ` because the ring
  instances of `AddMonoidAlgebra` there are noncomputable and opaque to
  kernel reduction (they pull classical instances): no value equality is
  checkable there by `rfl` or `decide`. With `LP`, on the contrary, every
  evaluation and distinction below is checked by `decide` (exact
  reduction in the kernel). A bridge `LP → LaurentPolynomial ℤ` (by a sum
  of monomials `T n`) is trivial to define in a later slice should
  Mathlib interop become necessary.

  ## Convention choice and chirality

  The A14 convention is chosen because under it the lake's trefoil
  (`trefoilDiagram`, three positive crossings according to its
  documentation) computes the textbook value for the right-handed trefoil:
  ⟨3₁⟩ = −A⁵ − A⁻³ + A⁻⁷. The dual convention (A joins e1–e2, e3–e4)
  exchanges A and A⁻¹ and yields the mirror trefoil bracket.

  ## Honest boundary (what this file does not prove)

  - **Reidemeister invariance**: NOT proved here. The Reidemeister moves
    (`Knots.Reidemeister_en`) are themselves sorries. The bracket is thus
    established as a *diagram* invariant, not yet a knot invariant: the
    distinction theorems below distinguish diagrams, and become knot
    distinctions once invariance is proved (future slice of the EPIC).
  - **Invariance of the Jones polynomial**: NOT proved, for the same
    reason. f(D) is built to be invariant (the factor (−A³)^(−w)
    compensates move I), but the `jones_*` theorems remain equalities of
    diagrams.
  - **`figureEightDiagram` code of `Knots.Basic_en`**: not planar
    (`figureEightDiagram_not_planar`). Fixing it touches other modules
    (Conway, Invariant) and the Lean-17c notebook; it is tracked by
    #17595. This slice does not modify `Knots.Basic_en`.
  - **Sign read off the labelling**: `crossingSign` assumes edges
    numbered consecutively along the orientation (KnotInfo/KnotAtlas
    convention). On a code that does not follow it, the sign is
    meaningless (it is 0 when the two over labels are not
    consecutive).
  - **Mirror sensitivity**: the writhe of the mirror is the negation of
    the writhe (`writhe_mirror`, a symbolic statement for every
    well-formed diagram). The relation V(mirror) = V(t⁻¹) is only checked
    on the trefoil (`jones_mirror_trefoil_eq_invert`); its general
    statement (mirror bracket = bracket under A ↔ A⁻¹) is not
    formalised.
-/

import Knots.Basic_en

namespace Knots_en

/-! ## Sparse Laurent polynomials (`LP`)

List of (exponent, coefficient) monomials in normal form: strictly
decreasing exponents, nonzero coefficients. All operations are computable
and reducible in the kernel.
-/

/-- Type of sparse Laurent polynomials: a list of (exponent, coefficient)
pairs in normal form (strictly decreasing exponents, nonzero
coefficients). -/
abbrev LP : Type := List (ℤ × ℤ)

/-- Insert-merges one monomial into an `LP` list sorted by decreasing
exponent (normal form preserved). -/
def lpMerge (p : ℤ × ℤ) : LP → LP
  | [] => if p.2 = 0 then [] else [p]
  | (m, d) :: rest =>
    if m > p.1 then (m, d) :: lpMerge p rest
    else if m = p.1 then (if d + p.2 = 0 then rest else (m, d + p.2) :: rest)
    else if p.2 = 0 then (m, d) :: rest else p :: (m, d) :: rest

/-- Puts an arbitrary list of monomials into normal form. -/
def lpNorm (l : LP) : LP := l.foldl (fun acc p => lpMerge p acc) []

/-- The monomial A^n (normal form). -/
def monoA (n : ℤ) : LP := [(n, 1)]

/-- δ = −A² − A⁻²: the value of one extra closed loop. -/
def deltaVar : LP := [(2, -1), (-2, -1)]

/-- Product of two monomial lists (not normalised: distributes;
normalisation happens at the `bracket` level). -/
def lpMul (p q : LP) : LP :=
  p.flatMap (fun (n, c) => q.map (fun (m, d) => (n + m, c * d)))

/-- Natural power of a monomial list. -/
def lpPow (p : LP) : Nat → LP
  | 0 => [(0, 1)]
  | k + 1 => lpMul (lpPow p k) p

/-! ## States and smoothings

A state is a `Bool` vector (`true` = A smoothing, `false` = B smoothing),
one Bool per crossing, in `KnotDiagram.crossings` order.
-/

/-- All `Bool` vectors of length `n`: the state space of a diagram with
`n` crossings. -/
def allBoolVectors : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBoolVectors n).flatMap (fun v => [true :: v, false :: v])

/-- The two connections produced by smoothing the crossing `c` in state
`s`.

Module convention A14: the A smoothing joins `e1–e4` and `e2–e3`, the B
smoothing joins `e1–e2` and `e3–e4`. See the file docstring for the
rationale (right-handed trefoil = textbook value). -/
def smoothingConnections (c : PDCrossing) (s : Bool) : List (Nat × Nat) :=
  if s then [(c.e1, c.e4), (c.e2, c.e3)] else [(c.e1, c.e2), (c.e3, c.e4)]

/-- Total connections of the state `v` of diagram `d` (two per smoothed
crossing). -/
def stateConnections (d : KnotDiagram) (v : List Bool) : List (Nat × Nat) :=
  (d.crossings.zip v).flatMap (fun (c, s) => smoothingConnections c s)

/-! ## Loops of a state

The loops are the connected components of the connection multigraph
(vertices = edge labels). They are computed by successive class merges
(naive union-find) starting from the trivial partition.
-/

/-- Merges the classes containing labels `a` and `b` in a partition of
edge labels. -/
def mergeClasses (classes : List (List Nat)) (a b : Nat) : List (List Nat) :=
  let ca := classes.flatMap (fun cl => if cl.contains a then [cl] else [])
  let cb := classes.flatMap (fun cl => if cl.contains b && !cl.contains a then [cl] else [])
  let kept := classes.filter (fun cl => !cl.contains a && !cl.contains b)
  let merged := ca.flatten ++ cb.flatten
  if merged.isEmpty then kept else kept ++ [merged]

/-- Initial partition: every label occurring in the connections forms its
own class. -/
def initialClasses (conns : List (Nat × Nat)) : List (List Nat) :=
  ((conns.flatMap (fun p => [p.1, p.2])).eraseDups).map (fun l => [l])

/-- Reduces the partition by merging along each connection (fuel = number
of connections). -/
def buildComponents : Nat → List (Nat × Nat) → List (List Nat) → List (List Nat)
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | fuel + 1, (a, b) :: rest, acc => buildComponents fuel rest (mergeClasses acc a b)

/-- Connected components of the connection multigraph. -/
def connectedComponents (conns : List (Nat × Nat)) : List (List Nat) :=
  buildComponents conns.length conns (initialClasses conns)

/-- Number of loops of the state carried by the connections `conns` (the
multigraph being 2-regular for a well-formed PD code, every connected
component is a cycle, i.e. a loop). -/
def connectionLoops (conns : List (Nat × Nat)) : Nat :=
  (connectedComponents conns).length

/-- Number of loops of diagram `d` smoothed according to state `v`.

Special case: a diagram without crossings (the PD code of the unknot) is
a single circle — one loop, no connections. -/
def stateLoops (d : KnotDiagram) (v : List Bool) : Nat :=
  match d.crossings with
  | [] => 1
  | _ => connectionLoops (stateConnections d v)

/-! ## Kauffman bracket
-/

/-- State monomial A^(#A − #B) for the smoothing vector `v`. -/
def stateMonomial (v : List Bool) : LP :=
  monoA ((v.count true : ℤ) - (v.count false : ℤ))

/-- State term: A^(#A − #B) · δ^(k−1) where `k` is the number of loops of
state `v` of diagram `d`. -/
def stateTerm (d : KnotDiagram) (v : List Bool) : LP :=
  lpMul (stateMonomial v) (lpPow deltaVar (stateLoops d v - 1))

/-- Kauffman bracket ⟨D⟩ of diagram `d`: sum (concatenation then
normalisation) of state terms over all states. -/
def bracket (d : KnotDiagram) : LP :=
  lpNorm (((allBoolVectors d.crossings.length).map (stateTerm d)).flatten)

/-! ## Evaluations and distinctions (decidable)

Values are confirmed by exact computation in the kernel (`decide` — the
`LP` representation is computable throughout). The trefoil gives the
textbook value for the right-handed trefoil (the rationale for
convention A14); the `figureEightDiagram` code gives A⁸ + 1 − A⁻⁴, which
is not the bracket of the figure-eight knot: this code is not planar
(slice 2).
-/

/-- The bracket of the unknot diagram is 1: unique empty state, one
loop, δ⁰. -/
theorem bracket_unknotDiagram : bracket unknotDiagram = [(0, 1)] := by
  decide

/-- Bracket value on the trefoil: ⟨3₁⟩ = −A⁵ − A⁻³ + A⁻⁷ (textbook value
for the right-handed trefoil, under module convention A14). -/
theorem bracket_trefoilDiagram :
    bracket trefoilDiagram = [(5, -1), (-3, -1), (-7, 1)] := by
  decide

set_option maxRecDepth 100000 in
/-- Bracket value on the `figureEightDiagram` code: A⁸ + 1 − A⁻⁴. This
code is not planar (`figureEightDiagram_not_planar`): the value is that
of a virtual knot, not the bracket of the figure-eight knot, which is
A⁸ − A⁴ + 1 − A⁻⁴ + A⁻⁸ (`bracket_figureEightPlanarDiagram`). -/
theorem bracket_figureEightDiagram :
    bracket figureEightDiagram = [(8, 1), (0, 1), (-4, -1)] := by
  decide

/-- The bracket distinguishes (at the diagram level) the trefoil from the
unknot: coefficient −1 at A⁵ versus 0. As long as Reidemeister
invariance of the bracket is unproved, this does not yet distinguish the
*knots* — see the honest boundary of the file. -/
theorem bracket_trefoil_ne_bracket_unknot :
    bracket trefoilDiagram ≠ bracket unknotDiagram := by
  decide

/-- The bracket distinguishes (at the diagram level) the
`figureEightDiagram` code from the unknot: coefficient 1 at A⁸ versus 0
— same caveat as `bracket_trefoil_ne_bracket_unknot`. -/
theorem bracket_figureEight_ne_bracket_unknot :
    bracket figureEightDiagram ≠ bracket unknotDiagram := by
  decide

/-! ## Slice 2 — crossing sign and writhe

A PD code carries no sign field, but its labelling determines the sign:
edges are numbered consecutively along the orientation of the knot
(KnotInfo/KnotAtlas convention), so the over strand runs from `e2` to
`e4` when `e4` follows `e2` (modulo `numEdges`), and from `e4` to `e2` in
the opposite case. In the module's clockwise reading (see
`Knots.Basic_en`), the crossing is positive in the first case: this is
what makes the three crossings of `trefoilDiagram` positive, as its
documentation states.

The field comments of `PDCrossing` call `e2` "over-in" and `e4`
"over-out": this only holds for a positive crossing. At a negative
crossing, the over strand enters through `e4`.
-/

/-- Cyclic successor of an edge label in `[1, n]`. -/
def nextEdge (n l : Nat) : Nat := l % n + 1

/-- Sign of crossing `c` in a diagram with `n` edges: `1` if the over
strand runs from `e2` to `e4`, `-1` if it runs from `e4` to `e2`, `0` if
the labelling does not decide (non-consecutive over labels). -/
def crossingSign (n : Nat) (c : PDCrossing) : ℤ :=
  if c.e4 = nextEdge n c.e2 then 1
  else if c.e2 = nextEdge n c.e4 then -1
  else 0

/-- Writhe of the diagram: sum of the signs of its crossings. -/
def writhe (d : KnotDiagram) : ℤ :=
  (d.crossings.map (crossingSign d.numEdges)).sum

/-- The two cases of `crossingSign` are exclusive: two labels of `[1, n]`
can follow each other both ways only if `n ≤ 2`. -/
theorem nextEdge_not_both {n a b : Nat} (hn : 3 ≤ n) (ha1 : 1 ≤ a) (han : a ≤ n)
    (hb1 : 1 ≤ b) (hbn : b ≤ n) : ¬ (b = nextEdge n a ∧ a = nextEdge n b) := by
  rintro ⟨h1, h2⟩
  unfold nextEdge at h1 h2
  rcases Nat.lt_or_ge a n with ha | ha
  · rw [Nat.mod_eq_of_lt ha] at h1
    rcases Nat.lt_or_ge b n with hb | hb
    · rw [Nat.mod_eq_of_lt hb] at h2
      omega
    · have hbe : b = n := by omega
      rw [hbe, Nat.mod_self] at h2
      omega
  · have hae : a = n := by omega
    rw [hae, Nat.mod_self] at h1
    rcases Nat.lt_or_ge b n with hb | hb
    · rw [Nat.mod_eq_of_lt hb] at h2
      omega
    · omega

/-- Mirroring (swapping over and under) negates the sign of a crossing
whose over labels lie in `[1, n]`, for `n ≥ 3`. -/
theorem crossingSign_mirrorCrossing {n : Nat} (c : PDCrossing) (hn : 3 ≤ n)
    (h2 : 1 ≤ c.e2 ∧ c.e2 ≤ n) (h4 : 1 ≤ c.e4 ∧ c.e4 ≤ n) :
    crossingSign n (mirrorCrossing c) = - crossingSign n c := by
  have hx := nextEdge_not_both hn h2.1 h2.2 h4.1 h4.2
  change (if c.e2 = nextEdge n c.e4 then (1 : ℤ)
    else if c.e4 = nextEdge n c.e2 then -1 else 0) =
    -(if c.e4 = nextEdge n c.e2 then (1 : ℤ)
      else if c.e2 = nextEdge n c.e4 then -1 else 0)
  by_cases hA : c.e4 = nextEdge n c.e2
  · have hB : ¬ c.e2 = nextEdge n c.e4 := fun h => hx ⟨hA, h⟩
    simp only [if_neg hB, if_pos hA]
  · by_cases hB : c.e2 = nextEdge n c.e4
    · simp only [if_pos hB, if_neg hA, neg_neg]
    · simp only [if_neg hB, if_neg hA, neg_zero]

/-- List version of `crossingSign_mirrorCrossing`: the sum of the signs
of a list of mirrored crossings is the negation of the original sum. -/
theorem sum_crossingSign_mirror {n : Nat} (hn : 3 ≤ n) :
    ∀ l : List PDCrossing,
      (∀ c ∈ l, (1 ≤ c.e2 ∧ c.e2 ≤ n) ∧ (1 ≤ c.e4 ∧ c.e4 ≤ n)) →
      ((l.map mirrorCrossing).map (crossingSign n)).sum = - (l.map (crossingSign n)).sum
  | [], _ => by simp
  | c :: l, h => by
    have hc := h c (by simp)
    have ih := sum_crossingSign_mirror hn l (fun c' hc' => h c' (by simp [hc']))
    simp only [List.map_cons, List.sum_cons]
    rw [crossingSign_mirrorCrossing c hn hc.1 hc.2, ih]
    omega

/-- A well-formed diagram has all its over labels in `[1, numEdges]`
(clause (a) of `KnotDiagram.wf`). -/
theorem KnotDiagram.wf_over_bounds {d : KnotDiagram} (hwf : d.wf = true) :
    ∀ c ∈ d.crossings,
      (1 ≤ c.e2 ∧ c.e2 ≤ d.numEdges) ∧ (1 ≤ c.e4 ∧ c.e4 ≤ d.numEdges) := by
  intro c hc
  have hne : d.crossings ≠ [] := List.ne_nil_of_mem hc
  unfold KnotDiagram.wf at hwf
  rw [if_neg hne] at hwf
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  have h2 : c.e2 ∈ d.edges := List.mem_flatMap.2 ⟨c, hc, by simp⟩
  have h4 : c.e4 ∈ d.edges := List.mem_flatMap.2 ⟨c, hc, by simp⟩
  exact ⟨hwf.1 _ h2, hwf.1 _ h4⟩

/-- The writhe of the mirror of a well-formed knot with at least three
edges is the negation of its writhe. Symbolic statement, valid for every
diagram. -/
theorem writhe_mirror (k : Knot) (hwf : k.diagram.wf = true)
    (hn : 3 ≤ k.diagram.numEdges) :
    writhe k.mirror.diagram = - writhe k.diagram :=
  sum_crossingSign_mirror hn k.diagram.crossings (KnotDiagram.wf_over_bounds hwf)

/-- Writhe of the trefoil: its three crossings are positive. -/
theorem writhe_trefoilDiagram : writhe trefoilDiagram = 3 := by
  decide

/-- Writhe of the mirror trefoil: −3, an instance of `writhe_mirror`. -/
theorem writhe_mirror_trefoil : writhe trefoil.mirror.diagram = -3 := by
  rw [writhe_mirror trefoil trefoil_wf (by decide)]
  decide

/-- Writhe of the lake's `figureEightDiagram` code: its four crossings
are positive. A minimal figure-eight diagram has writhe zero (the knot is
amphichiral): this value is a first hint of the defect of this code,
established by `figureEightDiagram_not_planar`. -/
theorem writhe_figureEightDiagram : writhe figureEightDiagram = 4 := by
  decide

/-! ## Slice 2 — planarity: faces of the combinatorial map

At each crossing, a PD code fixes the cyclic order of the four edge
endpoints: this is a rotation system of the underlying 4-regular graph
(crossings = vertices, code edges = edges), hence a combinatorial map,
that is, a cellular embedding into an oriented surface. Its faces are the
orbits, on darts (crossing, position), of the permutation "cross the
edge, then advance one position in the cyclic order of the arrival
crossing". For a connected diagram with `n ≥ 1` crossings (`n` vertices,
`2n` edges), Euler's formula `n − 2n + F = 2 − 2g` gives: the map is
planar (genus `g = 0`) if and only if `F = n + 2`.

A code that fails this test cannot be drawn in any plane: it is a
**virtual** knot diagram (Kauffman 1999, *Virtual knot theory*, European
Journal of Combinatorics 20, 663-690). The bracket and the Jones
polynomial remain computable on it, but they are no longer those of a
classical knot.
-/

/-- Edge label at position `p` (0 to 3) of crossing `c`. -/
def PDCrossing.edgeAt (c : PDCrossing) : Nat → Nat
  | 0 => c.e1
  | 1 => c.e2
  | 2 => c.e3
  | _ => c.e4

/-- The darts of the diagram: (crossing, position) pairs. -/
def KnotDiagram.darts (d : KnotDiagram) : List (Nat × Nat) :=
  (List.range d.crossings.length).flatMap (fun i => (List.range 4).map (fun p => (i, p)))

/-- Edge label carried by a dart. -/
def KnotDiagram.dartLabel (d : KnotDiagram) (x : Nat × Nat) : Nat :=
  match d.crossings[x.1]? with
  | some c => c.edgeAt x.2
  | none => 0

/-- The other endpoint of the edge carried by dart `x` (the dart itself
if its label appears only once, the case of an ill-formed code). -/
def KnotDiagram.opposite (d : KnotDiagram) (x : Nat × Nat) : Nat × Nat :=
  match (d.darts.filter (fun y => y != x && d.dartLabel y == d.dartLabel x)).head? with
  | some y => y
  | none => x

/-- Step of the face permutation: cross the edge, then advance one
position in the cyclic order of the arrival crossing. -/
def KnotDiagram.faceStep (d : KnotDiagram) (x : Nat × Nat) : Nat × Nat :=
  let y := d.opposite x
  (y.1, (y.2 + 1) % 4)

/-- Darts visited from `y` until returning to `x` (at most `fuel`
steps). -/
def KnotDiagram.orbitFrom (d : KnotDiagram) (x : Nat × Nat) :
    Nat → Nat × Nat → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, y => if y = x then [] else y :: d.orbitFrom x fuel (d.faceStep y)

/-- The face containing dart `x`: its orbit under `faceStep`. -/
def KnotDiagram.face (d : KnotDiagram) (x : Nat × Nat) : List (Nat × Nat) :=
  x :: d.orbitFrom x d.darts.length (d.faceStep x)

/-- Counts faces by removing, face after face, the visited darts. -/
def KnotDiagram.countFaces (d : KnotDiagram) : Nat → List (Nat × Nat) → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | fuel + 1, x :: rest =>
    let f := d.face x
    1 + d.countFaces fuel (rest.filter (fun y => !f.contains y))

/-- Number of faces of the combinatorial map of the PD code. -/
def KnotDiagram.faceCount (d : KnotDiagram) : Nat :=
  d.countFaces d.darts.length d.darts

/-- Euler planarity criterion: `F = n + 2`. The crossingless diagram (an
embedded circle) is planar by convention. -/
def KnotDiagram.planar (d : KnotDiagram) : Bool :=
  d.crossings.isEmpty || d.faceCount == d.crossings.length + 2

/-- The trefoil has 5 faces for 3 crossings: 3 + 2, it is planar. -/
theorem faceCount_trefoilDiagram : trefoilDiagram.faceCount = 5 := by
  decide

theorem trefoilDiagram_planar : trefoilDiagram.planar = true := by
  decide

/-- The mirror of the trefoil stays planar: swapping positions 1 and 3
reverses the cyclic order at every crossing, which reflects the map
without changing its faces. -/
theorem mirror_trefoil_planar : trefoil.mirror.diagram.planar = true := by
  decide

/-- The lake's `figureEightDiagram` code has only 4 faces for 4
crossings, instead of the 6 of a planar diagram: its map has genus 1
(torus). -/
theorem faceCount_figureEightDiagram : figureEightDiagram.faceCount = 4 := by
  decide

/-- **The `figureEightDiagram` code of `Knots.Basic_en` is not a planar
diagram.** It describes a virtual knot: its bracket and Jones values are
not those of the figure-eight knot (see `jones_figureEightDiagram`). -/
theorem figureEightDiagram_not_planar : figureEightDiagram.planar = false := by
  decide

/-- A planar PD code of the figure-eight knot: the KnotAtlas one
(`X[4,2,5,1], X[8,6,1,5], X[6,3,7,4], X[2,7,3,8]`). Read in the module's
clockwise convention, it describes the mirror of the KnotAtlas diagram,
which is still a figure-eight knot since that knot is amphichiral. -/
def figureEightPlanarDiagram : KnotDiagram where
  crossings := [
    ⟨4, 2, 5, 1⟩,
    ⟨8, 6, 1, 5⟩,
    ⟨6, 3, 7, 4⟩,
    ⟨2, 7, 3, 8⟩
  ]
  numEdges := 8

theorem figureEightPlanarDiagram_wf : figureEightPlanarDiagram.wf = true := by
  decide

theorem faceCount_figureEightPlanarDiagram : figureEightPlanarDiagram.faceCount = 6 := by
  decide

theorem figureEightPlanarDiagram_planar : figureEightPlanarDiagram.planar = true := by
  decide

/-- Two positive and two negative crossings: writhe zero, as expected
from a minimal diagram of an amphichiral knot. -/
theorem writhe_figureEightPlanarDiagram : writhe figureEightPlanarDiagram = 0 := by
  decide

set_option maxRecDepth 100000 in
/-- Bracket of the planar figure eight: A⁸ − A⁴ + 1 − A⁻⁴ + A⁻⁸, the
textbook value, symmetric under A ↔ A⁻¹. -/
theorem bracket_figureEightPlanarDiagram :
    bracket figureEightPlanarDiagram = [(8, 1), (4, -1), (0, 1), (-4, -1), (-8, 1)] := by
  decide

/-! ## Slice 2 — Jones polynomial

Kauffman's normalised polynomial f(D) = (−A³)^(−w(D)) · ⟨D⟩ compensates
the factor −A^(±3) the bracket picks up under a Reidemeister I move
(Kauffman 1987, *State models and the Jones polynomial*, Topology 26,
395-407). The Jones polynomial follows by A = t^(−1/4): V(t) =
f(D)|_{A = t^(−1/4)}. For a knot, all exponents of f(D) are multiples of
4; the `kauffmanF_*` theorems exhibit this on the instances.
-/

/-- Kauffman's normalised polynomial f(D) = (−A³)^(−w(D)) · ⟨D⟩. -/
def kauffmanF (d : KnotDiagram) : LP :=
  let w := writhe d
  lpNorm (lpMul [(-3 * w, if w % 2 = 0 then 1 else -1)] (bracket d))

/-- Change of variable A = t^(−1/4): exponent `e` of A becomes `−e/4` in
t (exact division when `e` is a multiple of 4). -/
def lpAtoT (p : LP) : LP := lpNorm (p.map (fun m => (-(m.1 / 4), m.2)))

/-- Jones polynomial V(t) of diagram `d`, in normal form (variable t). -/
def jones (d : KnotDiagram) : LP := lpAtoT (kauffmanF d)

/-- Substitution t ↦ t⁻¹, which maps the Jones polynomial of a knot to
that of its mirror. -/
def lpInvert (p : LP) : LP := lpNorm (p.map (fun m => (-m.1, m.2)))

theorem jones_unknotDiagram : jones unknotDiagram = [(0, 1)] := by
  decide

/-- f(3₁) = A⁻⁴ + A⁻¹² − A⁻¹⁶: exponents are multiples of 4. -/
theorem kauffmanF_trefoilDiagram :
    kauffmanF trefoilDiagram = [(-4, 1), (-12, 1), (-16, -1)] := by
  decide

/-- V(3₁) = −t⁴ + t³ + t: Jones polynomial of the right-handed trefoil. -/
theorem jones_trefoilDiagram : jones trefoilDiagram = [(4, -1), (3, 1), (1, 1)] := by
  decide

/-- V(3₁ mirror) = t⁻¹ + t⁻³ − t⁻⁴: left-handed trefoil. -/
theorem jones_mirror_trefoil :
    jones trefoil.mirror.diagram = [(-1, 1), (-3, 1), (-4, -1)] := by
  decide

/-- On the trefoil, the mirror acts on Jones by t ↦ t⁻¹. -/
theorem jones_mirror_trefoil_eq_invert :
    jones trefoil.mirror.diagram = lpInvert (jones trefoilDiagram) := by
  decide

/-- The Jones polynomial distinguishes the trefoil diagram from its
mirror (the bracket alone could too, but only f(D) is meant to become a
knot invariant). Same caveat as slice 1: as long as Reidemeister
invariance is unproved, this is a distinction of diagrams, not yet the
chirality of the trefoil. -/
theorem jones_trefoil_ne_mirror :
    jones trefoilDiagram ≠ jones trefoil.mirror.diagram := by
  decide

set_option maxRecDepth 100000 in
/-- V(4₁) = t² − t + 1 − t⁻¹ + t⁻²: textbook value for the figure-eight
knot. -/
theorem jones_figureEightPlanarDiagram :
    jones figureEightPlanarDiagram = [(2, 1), (1, -1), (0, 1), (-1, -1), (-2, 1)] := by
  decide

set_option maxRecDepth 100000 in
/-- The Jones polynomial of the figure eight is invariant under
t ↦ t⁻¹, the signature of the knot's amphichirality. -/
theorem jones_figureEightPlanarDiagram_invert :
    lpInvert (jones figureEightPlanarDiagram) = jones figureEightPlanarDiagram := by
  decide

set_option maxRecDepth 100000 in
/-- The trefoil and the figure eight have distinct Jones polynomials. -/
theorem jones_figureEightPlanar_ne_trefoil :
    jones figureEightPlanarDiagram ≠ jones trefoilDiagram := by
  decide

set_option maxRecDepth 100000 in
/-- **Defect of the lake's `figureEightDiagram` code**: its Jones
polynomial is that of the right-handed trefoil, not that of the
figure-eight knot. Together with `figureEightDiagram_not_planar`, this
theorem establishes that the code describes a virtual knot; the slice 1
values computed on it (`bracket_figureEightDiagram`) concern that virtual
knot. -/
theorem jones_figureEightDiagram :
    jones figureEightDiagram = jones trefoilDiagram := by
  decide

end Knots_en

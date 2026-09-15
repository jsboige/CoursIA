/-
  Knots.Jones_en — Kauffman bracket on PD codes (slice 1)
  ====================================================================

  This file defines the Kauffman bracket ⟨D⟩ of a knot diagram given as a
  PD code (see `Knots.Basic_en`) as a state sum, evaluates it on the three
  named diagrams of the lake (unknot, trefoil, figure eight), and derives
  the computational distinctions trefoil ≠ unknot and figure eight ≠
  unknot.

  Slice 1 of Phase 4 of EPIC #2874 (Jones polynomial via the Kauffman
  bracket). Jones normalisation (writhe) is out of scope for this slice:
  `PDCrossing` carries no sign field, so the writhe is not computable
  without extending `Knots.Basic_en` (future slice).

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
  - **Writhe / Jones polynomial**: NOT defined. `PDCrossing` has no sign
    field; the writhe (and hence the normalisation f(D) =
    (−A)^(−3w)·⟨D⟩) requires extending `Knots.Basic_en` — outside the
    files of this slice.
  - **Mirror sensitivity**: the bracket of a mirrored diagram is obtained
    by exchanging A ↔ A⁻¹ (numerically verified in Python on the trefoil,
    not formalised here).
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
convention A14), the figure eight gives A⁸ + 1 − A⁻⁴.
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
/-- Bracket value on the figure eight: A⁸ + 1 − A⁻⁴. -/
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

/-- The bracket distinguishes (at the diagram level) the figure eight
from the unknot: coefficient 1 at A⁸ versus 0 — same caveat as
`bracket_trefoil_ne_bracket_unknot`. -/
theorem bracket_figureEight_ne_bracket_unknot :
    bracket figureEightDiagram ≠ bracket unknotDiagram := by
  decide

end Knots_en

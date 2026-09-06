import Mathlib.Logic.Relation
import Percolation.Connectivity_en

/-! # Finite kernel of percolation — components and boundary (tranche 3)

Continuation of the finite kernel (see `Percolation/Connectivity_en.lean`). This
module ties together three notions: the **open connected component** of a vertex,
the property of being **closed along open edges** (no open edge leaves it), and
the **boundary** (the complement). The central bridge is the
connection↔component↔boundary lemma: a set is ω-closed if and only if it is a
union of connected components (it contains the component of each of its
elements), if and only if no open edge links it to its complement (empty
boundary).

On a finite simple graph `G` and a configuration `ω` of **open** edges, the
component `Component ω v` is the set of vertices reachable from `v` by a path of
open edges (the reflexive-transitive closure of the open adjacency).

i18n convention EPIC #4980: docstrings in English here; the French mirror lives
in `Percolation/Components.lean` (byte-identical apart from docstrings/comments).
-/

set_option linter.unusedSectionVars false

namespace Percolation_en

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [Fintype (Edge G)] [DecidableEq (Edge G)]

/-- **Open connected component** of a vertex `v`: the set of vertices `w`
reachable from `v` in the configuration `ω` (path of open edges). -/
def Component (ω : Finset (Edge G)) (v : V) : Set V :=
  {w : V | ConnectedIn G ω v w}

/-- **Closed along open edges**: `A` is ω-closed if no open edge leaves it — any
`u ∈ A` openly adjacent to `v` forces `v ∈ A`. -/
def openEdgeClosed (ω : Finset (Edge G)) (A : Set V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ A → openAdj G ω u v → v ∈ A

/-- **A vertex belongs to its own component** (reflexivity). -/
theorem component_self {ω : Finset (Edge G)} (v : V) : v ∈ Component G ω v := by
  unfold Component
  exact Relation.ReflTransGen.refl

/-- **The component is ω-closed**: no open edge leaves it. This is the first
face of the component↔boundary link. -/
theorem component_closed {ω : Finset (Edge G)} (v : V) : openEdgeClosed G ω (Component G ω v) := by
  intro u w hu huw
  unfold Component at hu ⊢
  exact Relation.ReflTransGen.trans hu (Relation.ReflTransGen.single huw)

/-- **Connectivity↔component bridge**: `w ∈ Component v` if and only if `v` and
`w` are connected. Definitional (the component IS the set of the connected). -/
theorem component_iff_connected {ω : Finset (Edge G)} (v w : V) :
    w ∈ Component G ω v ↔ ConnectedIn G ω v w := by
  rfl

/-- **Adjacency implies membership in the component**: an open edge leaving `u`
places its endpoint in the component of `u`. -/
theorem mem_component_of_adj {ω : Finset (Edge G)} {u v : V} (hAdj : openAdj G ω u v) :
    v ∈ Component G ω u := by
  unfold Component
  exact Relation.ReflTransGen.single hAdj

/-- **A closed set contains the component of each of its elements**: if `A` is
ω-closed and contains `u`, it contains every vertex reachable from `u`
(induction along the path of open edges). -/
theorem openEdgeClosed.mem_of_connected {ω : Finset (Edge G)} {A : Set V}
    (h : openEdgeClosed G ω A) {u w : V} (hu : u ∈ A) (hconn : ConnectedIn G ω u w) : w ∈ A := by
  induction hconn with
  | refl => exact hu
  | tail hconn2 hstep ih => exact h ih hstep

/-- **Closed ⟺ empty boundary**: `A` is ω-closed if and only if no open edge
links `A` to its complement. This is the « boundary » face (second face of the
link). -/
theorem openEdgeClosed_iff_no_cross {ω : Finset (Edge G)} (A : Set V) :
    openEdgeClosed G ω A ↔ ∀ ⦃u v : V⦄, u ∈ A → v ∉ A → ¬ openAdj G ω u v := by
  constructor
  · intro h u v hu hvnot hAdj
    exact hvnot (h hu hAdj)
  · intro h u v hu hAdj
    by_contra hvnot
    exact (h hu hvnot) hAdj

/-- **Connection↔component↔boundary lemma**: `A` is ω-closed if and only if it
is a union of connected components (contains the component of each of its
elements). It is the kernel bridge: the empty boundary (no open edge leaves `A`)
is equivalent to « `A` is a union of components ». -/
theorem openEdgeClosed_iff_contains_components {ω : Finset (Edge G)} (A : Set V) :
    openEdgeClosed G ω A ↔ ∀ ⦃u : V⦄, u ∈ A → Component G ω u ⊆ A := by
  constructor
  · intro h u hu w hw
    exact openEdgeClosed.mem_of_connected (G := G) h hu (by simpa [Component] using hw)
  · intro h u v hu hAdj
    exact h hu (mem_component_of_adj (G := G) hAdj)

end Percolation_en

import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Logic.Relation

/-! # Finite kernel of percolation — connectivity (tranche 2)

Continuation of the finite kernel (see `Percolation/Basic_en.lean`). This module
establishes that the event « two vertices are connected » is an **increasing**
event (monotone with respect to the inclusion of open edges): more open edges
can only preserve it. It is precisely the property that makes connectivity
events eligible for the **Harris–Kleitman** inequality (finite FKG) proved in
milestone 1.

On a finite simple graph `G` and a set `ω` of **open** edges (a
configuration), two vertices `u` and `v` are *connected* if there is a path of
open edges joining them — the reflexive-transitive closure of the relation
« `u` and `v` are adjacent by an open edge ».

i18n convention EPIC #4980: docstrings in English here; the French mirror lives
in `Percolation/Connectivity.lean` (byte-identical apart from docstrings/comments).
-/

-- The monotonicity lemmas `openAdj_mono`/`connected_mono` reason about the
-- inclusion of `Finset (Edge G)` without needing the finiteness instances
-- (used by the events `connectedEvent`): we turn the linter warning off.
set_option linter.unusedSectionVars false

namespace Percolation_en

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The type of the edges of a finite simple graph `G`: an unordered pair
`{u, v}` (`Sym2 V`) belonging to the edge set `G.edgeSet`. -/
abbrev Edge (G : SimpleGraph V) := {e : Sym2 V // e ∈ G.edgeSet}

variable (G : SimpleGraph V) [Fintype (Edge G)] [DecidableEq (Edge G)]

/-- **Open adjacency**: in the configuration `ω` (set of open edges), `u` and
`v` are adjacent if they are in `G` and if the edge `s(u, v)` is open (belongs
to `ω`). -/
abbrev openAdj (ω : Finset (Edge G)) (u v : V) : Prop :=
  ∃ (huv : G.Adj u v), (⟨s(u, v), (show s(u, v) ∈ G.edgeSet from huv)⟩ : Edge G) ∈ ω

/-- **Connectivity by open edges**: `u` and `v` are connected in the
configuration `ω` if there is a path of open edges joining them
(reflexive-transitive closure of `openAdj`). -/
abbrev ConnectedIn (ω : Finset (Edge G)) (u v : V) : Prop :=
  Relation.ReflTransGen (openAdj G ω) u v

/-- **Monotonicity of open adjacency**: if `ω₁ ⊆ ω₂` (more open edges), then
every open adjacency in `ω₁` also holds in `ω₂`. -/
lemma openAdj_mono {ω₁ ω₂ : Finset (Edge G)} (h : ω₁ ⊆ ω₂) :
    openAdj G ω₁ ≤ openAdj G ω₂ := by
  intro u v huv
  rcases huv with ⟨huv_adj, hmem⟩
  exact ⟨huv_adj, h hmem⟩

/-- **Monotonicity of connectivity**: if `ω₁ ⊆ ω₂`, then every pair connected
in `ω₁` remains connected in `ω₂`. The connectivity event is therefore
**increasing**. -/
lemma connected_mono {ω₁ ω₂ : Finset (Edge G)} (h : ω₁ ⊆ ω₂) :
    ConnectedIn G ω₁ ≤ ConnectedIn G ω₂ := by
  intro u v h_conn
  exact Relation.ReflTransGen.mono (openAdj_mono G h) u v h_conn

/-- **Connectivity event**: the family of configurations `ω` in which `u` and
`v` are connected, viewed as a `Finset` of configurations. -/
noncomputable def connectedEvent (u v : V) : Finset (Finset (Edge G)) :=
  Finset.univ.filter (fun ω : Finset (Edge G) => ConnectedIn G ω u v)

/-- **The connectivity event is increasing**: it is an `IsUpperSet` for the
inclusion order on configurations — more open edges preserves connectivity. -/
theorem connectedEvent_isUpperSet {u v : V} :
    IsUpperSet (connectedEvent G u v : Set (Finset (Edge G))) := by
  intro ω₁ ω₂ hsub hm
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    connected_mono G hsub u v (Finset.mem_filter.mp hm).2⟩

/-- **Harris–Kleitman (finite FKG) for connectivity**: two increasing
connectivity events correlate positively under the uniform measure on the
Boolean cube of edges. This is the milestone-1 bridge toward percolation: since
connectivity is an increasing event, it is eligible for the association
inequality. -/
theorem harris_kleitman_connected {u v x y : V} :
    #(connectedEvent G u v) * #(connectedEvent G x y) ≤
      2 ^ Fintype.card (Edge G) * #((connectedEvent G u v) ∩ (connectedEvent G x y)) :=
  (connectedEvent_isUpperSet G (u := u) (v := v)).le_card_inter_finset
    (connectedEvent_isUpperSet G (u := x) (v := y))

end Percolation_en

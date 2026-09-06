import Percolation.Components_en
import Percolation.Examples_en
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! # Finite percolation kernel — isoperimetric boundary (tranche 4)

Sequel of the finite kernel (see `Percolation/Components_en.lean`). This module
completes the components / connectivity / boundary trilogy by the **finite
isoperimetric** side: quantifying and characterising the **boundary** of a set
`A` in a configuration `ω` of open edges.

- `openEdgeCrosses`: an **open crossing** edge from `A` to its complement — an
  element of the boundary of `A`.
- `not_closed_iff_exists_crossing`: empty boundary ⟺ closed set (the dual of
  `openEdgeClosed_iff_no_cross` from tranche 3).
- `closed_eq_empty_or_univ_of_connected`: **the isoperimetric lemma** — in a
  configuration where every vertex is connected to every other (ω-connected
  graph), the only ω-closed sets are `∅` and the universe. Every nonempty proper
  set therefore has a nonempty boundary.
- The **C₃/C₄ bounds**: on the triangle and the square in the full configuration,
  the only closed sets are trivial.

Convention i18n EPIC #4980: English docstrings here; the French sibling lives in
`Percolation/Boundary.lean` (byte-identical outside docstrings/comments).
-/

set_option linter.unusedSectionVars false

namespace Percolation_en

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [Fintype (Edge G)] [DecidableEq (Edge G)]

/-- **Open crossing edge**: an open edge links an element of `A` to its
complement — an element of the boundary of `A` in the configuration `ω`. -/
def openEdgeCrosses (ω : Finset (Edge G)) (A : Set V) (u v : V) : Prop :=
  u ∈ A ∧ v ∉ A ∧ openAdj G ω u v

/-- **Empty boundary ⟺ closed**: `A` is ω-closed if and only if no open edge
crosses its boundary (no element of `A` is openly adjacent to its complement).
This is the dual of `openEdgeClosed_iff_no_cross`. -/
theorem not_closed_iff_exists_crossing {ω : Finset (Edge G)} (A : Set V) :
    ¬ openEdgeClosed G ω A ↔ ∃ u v : V, openEdgeCrosses G ω A u v := by
  rw [openEdgeClosed_iff_no_cross]
  constructor
  · intro h
    apply by_contra
    intro hnone
    apply h
    intro u v hu hvnot hAdj
    exact hnone ⟨u, v, hu, hvnot, hAdj⟩
  · intro h hclosed
    rcases h with ⟨u, v, hu, hvnot, hAdj⟩
    exact (hclosed (u := u) (v := v) hu hvnot) hAdj

/-- **Isoperimetric — the boundary lemma**: in a configuration `ω` where every
vertex is connected to every other (ω-connected graph), the only ω-closed sets
are `∅` and the universe. Every nonempty proper set therefore has a nonempty
boundary. The proof is the components↔boundary bridge: a nonempty closed set
contains the (open connected) component of each of its elements, which, by
ω-connectivity, is the whole universe. -/
theorem closed_eq_empty_or_univ_of_connected {ω : Finset (Edge G)} (A : Set V)
    (hconn : ∀ u v : V, ConnectedIn G ω u v) :
    openEdgeClosed G ω A ↔ A = Set.univ ∨ A = ∅ := by
  constructor
  · intro hclosed
    by_cases hA : A = ∅
    · exact Or.inr hA
    · left
      apply Set.eq_univ_iff_forall.mpr
      intro v
      rcases Set.nonempty_iff_ne_empty.mpr hA with ⟨u, hu⟩
      exact openEdgeClosed.mem_of_connected (G := G) hclosed hu (hconn u v)
  · intro htriv
    rcases htriv with hAuniv | hAempty
    · intro u v hu hAdj
      rw [hAuniv]
      simp
    · intro u v hu hAdj
      exfalso
      rw [hAempty] at hu
      simp at hu

/-- In the full configuration `full3`, every edge of `C₃` is open. -/
theorem openAdj_C3 {a b : Fin 3} (h : C3.Adj a b) : openAdj C3 full3 a b := by
  use h
  simp [full3]

/-- **`C₃` is ω-connected in the full configuration**: every vertex is connected
to every other (in the complete graph, a single step suffices). This is the
hypothesis of `closed_eq_empty_or_univ_of_connected`. -/
theorem C3_full_connected : ∀ a b : Fin 3, ConnectedIn C3 full3 a b := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (openAdj_C3 (by decide : C3.Adj (0 : Fin 3) 1))
  · exact Relation.ReflTransGen.single (openAdj_C3 (by decide : C3.Adj (0 : Fin 3) 2))
  · exact Relation.ReflTransGen.single (openAdj_C3 (by decide : C3.Adj (1 : Fin 3) 0))
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (openAdj_C3 (by decide : C3.Adj (1 : Fin 3) 2))
  · exact Relation.ReflTransGen.single (openAdj_C3 (by decide : C3.Adj (2 : Fin 3) 0))
  · exact Relation.ReflTransGen.single (openAdj_C3 (by decide : C3.Adj (2 : Fin 3) 1))
  · exact Relation.ReflTransGen.refl

/-- **`C₃` bound**: on the triangle in the full configuration, the only closed
sets are `∅` and the universe. No singleton nor nonempty proper pair is closed. -/
theorem C3_closed_iff (A : Set (Fin 3)) :
    openEdgeClosed C3 full3 A ↔ A = Set.univ ∨ A = ∅ :=
  closed_eq_empty_or_univ_of_connected C3 (A := A) (ω := full3) C3_full_connected

/-- In the full configuration `full4`, every edge of `C₄` is open. -/
theorem openAdj_C4 {a b : Fin 4} (h : C4.Adj a b) : openAdj C4 full4 a b := by
  use h
  simp [full4]

/-- **`C₄` is ω-connected in the full configuration**: every vertex is connected
to every other, by **composing** `Relation.ReflTransGen.trans` for the
non-adjacent pairs (`0—2` via `0—1—2`, `1—3` via `1—0—3`). -/
theorem C4_full_connected : ∀ a b : Fin 4, ConnectedIn C4 full4 a b := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (0 : Fin 4) 1))
  · exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (0 : Fin 4) 1)))
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (1 : Fin 4) 2)))
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (0 : Fin 4) 3))
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (1 : Fin 4) 0))
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (1 : Fin 4) 2))
  · exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (1 : Fin 4) 0)))
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (0 : Fin 4) 3)))
  · exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (2 : Fin 4) 1)))
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (1 : Fin 4) 0)))
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (2 : Fin 4) 1))
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (2 : Fin 4) 3))
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (3 : Fin 4) 0))
  · exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (3 : Fin 4) 0)))
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (0 : Fin 4) 1)))
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (3 : Fin 4) 2))
  · exact Relation.ReflTransGen.refl

/-- **`C₄` bound**: on the square in the full configuration, the only closed
sets are `∅` and the universe. No singleton nor nonempty proper pair is closed,
even without a direct edge between opposite vertices. -/
theorem C4_closed_iff (A : Set (Fin 4)) :
    openEdgeClosed C4 full4 A ↔ A = Set.univ ∨ A = ∅ :=
  closed_eq_empty_or_univ_of_connected C4 (A := A) (ω := full4) C4_full_connected

-- ============================================================
-- Finite boundary `∂A` and isoperimetric profile (tranche 4 complement)
-- ============================================================
variable (G : SimpleGraph V) [Fintype (Edge G)] [DecidableEq (Edge G)] [DecidableRel G.Adj]

/-- **Finite boundary `∂A`**: the `Finset` of **open** crossing edges — an open edge `s(u,v)`
belongs to `∂A` if `u ∈ A`, `v ∉ A` and the edge is open (in `ω`). This is the finite object of
the isoperimetric profile: `#(∂A)` counts the open edges leaving `A`. -/
def boundary (ω : Finset (Edge G)) (A : Finset V) : Finset (Edge G) :=
  ω.filter (fun e : Edge G =>
    ∃ (u : V) (v : V) (huv : G.Adj u v),
      u ∈ A ∧ v ∉ A ∧ e = ⟨s(u, v), (show s(u, v) ∈ G.edgeSet from huv)⟩)

/-- **Membership in `∂A`**: `e ∈ ∂A` if and only if `e` is an open edge (in `ω`) one of whose
endpoints is in `A` and the other in the complement. -/
theorem mem_boundary_iff (ω : Finset (Edge G)) (A : Finset V) (e : Edge G) :
    e ∈ boundary G ω A ↔ e ∈ ω ∧ ∃ (u : V) (v : V) (huv : G.Adj u v),
      u ∈ A ∧ v ∉ A ∧ e = ⟨s(u, v), (show s(u, v) ∈ G.edgeSet from huv)⟩ := by
  simp [boundary]

/-- **`∂A` empty ⟺ `A` ω-closed**: a finite set has an empty open boundary if and only if it is
ω-closed (no open edge leaves it). This is the **finite and quantitative** version of the
`openEdgeClosed_iff_no_cross` bridge of tranche 3: it links the `boundary` object to the
`openEdgeClosed` predicate by expressing closure as the vanishing of `#(∂A)`. -/
theorem boundary_empty_iff_closed (ω : Finset (Edge G)) (A : Finset V) :
    boundary G ω A = ∅ ↔ openEdgeClosed G ω (↑A : Set V) := by
  rw [openEdgeClosed_iff_no_cross]
  constructor
  · intro hboundary u v hu hvnot hAdj
    rcases hAdj with ⟨huv, hmem⟩
    let e : Edge G := ⟨s(u, v), (show s(u, v) ∈ G.edgeSet from huv)⟩
    have hmem' : e ∈ ω ∧ ∃ (u : V) (v : V) (huv : G.Adj u v),
        u ∈ A ∧ v ∉ A ∧ e = ⟨s(u, v), (show s(u, v) ∈ G.edgeSet from huv)⟩ := by
      refine ⟨hmem, u, v, huv, hu, hvnot, ?_⟩
      rfl
    have hmemb : e ∈ boundary G ω A := (mem_boundary_iff G ω A e).mpr hmem'
    rw [hboundary] at hmemb
    simp at hmemb
  · intro hclosed
    ext e
    constructor
    · intro he
      rcases (mem_boundary_iff G ω A e).mp he with ⟨heω, u, v, huv, hu, hvnot, heq⟩
      subst heq
      exact False.elim ((hclosed (u := u) (v := v) hu hvnot) ⟨huv, heω⟩)
    · intro heempty
      simp at heempty

/-- **`C₃` bound (isoperimetric profile)**: in the full configuration, every nonempty proper
`A ⊆ C₃` has boundary cardinality exactly `2` — the triangle being complete, every vertex of `A`
is openly adjacent to every vertex of the complement (`|A|·(3−|A|) = 2` on a triangle, for
`|A| ∈ {1,2}`). The minimum `min_{|A|=k}|∂A|` is therefore **2** for `k ∈ {1,2}`. -/
theorem boundary_card_C3 : ∀ A : Finset (Fin 3), A.Nonempty → A ≠ Finset.univ →
    #(boundary C3 full3 A) = 2 := by
  decide

/-- **`C₃` lower bound**: `2 ≤ #(∂A)` for every nonempty proper subset of the triangle (the
`≥ 2` component of the profile). -/
theorem two_le_boundary_C3 : ∀ A : Finset (Fin 3), A.Nonempty → A ≠ Finset.univ →
    2 ≤ #(boundary C3 full3 A) := by
  intro A hne hproper
  exact (boundary_card_C3 A hne hproper).ge

/-- **`C₄` lower bound (isoperimetric profile)**: in the full configuration of the square, every
nonempty proper `A ⊆ C₄` has boundary cardinality at least `2`. The minimum `min_{|A|=k}|∂A|` is
at least `2` for every `1 ≤ k ≤ 3`. -/
theorem two_le_boundary_C4 : ∀ A : Finset (Fin 4), A.Nonempty → A ≠ Finset.univ →
    2 ≤ #(boundary C4 full4 A) := by
  decide

/-- **Attainment of the `C₄` minimum (cardinal `1`)**: the singleton `{0}` has boundary exactly `2`
(the edges `0—1` and `0—3`) — the minimum value at cardinal `k = 1`. The cardinals `k = 2` and
`k = 3` are attained by the witnesses `{0,1}` (`boundary_card_C4_adjacent`) and `{0,1,2}`
(`boundary_card_C4_triple`), so together with `two_le_boundary_C4` the profile `min_{|A|=k}|∂A| = 2`
is established for every `1 ≤ k ≤ 3`. -/
theorem boundary_attains_min_C4 :
    ∃ A : Finset (Fin 4), A.Nonempty ∧ A ≠ Finset.univ ∧ #(boundary C4 full4 A) = 2 := by
  refine ⟨{0}, by simp, by simp, by decide⟩

/-- **Square: adjacent pair**: `{0,1}` has boundary cardinality `2` (edges `1—2` and `0—3`) —
the witness attaining the minimum at cardinal `k = 2`. -/
theorem boundary_card_C4_adjacent : #(boundary C4 full4 ({0, 1} : Finset (Fin 4))) = 2 := by
  decide

/-- **Square: triple**: `{0,1,2}` has boundary cardinality `2` (edges `2—3` and `0—3`) —
the witness attaining the minimum at cardinal `k = 3`. -/
theorem boundary_card_C4_triple : #(boundary C4 full4 ({0, 1, 2} : Finset (Fin 4))) = 2 := by
  decide

/-- **Square: opposite pair**: `{0,2}` (opposite, non-adjacent endpoints) has boundary cardinality
`4` — the four edges `0—1`, `0—3`, `2—1`, `2—3` leave `A`. This case **exercises** the absence of a
direct `0—2` edge and distinguishes `C₄` from the triangle. -/
theorem boundary_card_C4_opposite : #(boundary C4 full4 ({0, 2} : Finset (Fin 4))) = 4 := by
  decide

end Percolation_en

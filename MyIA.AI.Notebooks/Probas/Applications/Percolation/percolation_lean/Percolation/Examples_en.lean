import Percolation.Components_en
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! # Finite kernel of percolation — a calculable example (tranche 3, acceptance 3)

Concrete instance of the components/boundary kernel on the **triangle** `C₃`
(`SimpleGraph.cycleGraph 3`). In `cycleGraph 3` every pair of vertices is
adjacent (modular subtraction), so `C₃` is the complete graph on `Fin 3`: its
edge set has cardinal 3, and the full configuration `full3` (all edges open)
makes the whole graph connected.

This module grounds the abstract lemmas of
`Percolation/Components_en.lean` on a small finite graph — the « calculable
example » of issue #14871, acceptance 3 — and is checkable by `lake build`.

- `component_C3_full`: in the full configuration the open component of `0` is
  the whole vertex set.
- `not_openEdgeClosed_C3_singleton`: the singleton `{0}` is **not** ω-closed.
- `exists_boundary_edge_C3`: the open edge `0—1` crosses from `{0}` to its
  complement — a concrete boundary witness.
-/

set_option linter.unusedSectionVars false

namespace Percolation_en

open Finset

/-- **Triangle** `C₃` — the 3-cycle, a concrete finite simple graph. In
`SimpleGraph.cycleGraph 3` every pair of vertices is adjacent, so `C₃` is the
complete graph on `Fin 3`. -/
abbrev C3 : SimpleGraph (Fin 3) := SimpleGraph.cycleGraph 3

/-- **Full configuration** on `C₃`: every edge is open. -/
abbrev full3 : Finset (Edge C3) := Finset.univ

/-- `C₃` has exactly three (openable) edges. -/
theorem card_edge_C3 : Fintype.card (Edge C3) = 3 := by
  decide

/-- In `C₃` the vertices `0` and `1` are adjacent. -/
theorem adj_C3_0_1 : (SimpleGraph.cycleGraph 3).Adj (0 : Fin 3) 1 := by
  decide

/-- In `C₃` the vertices `0` and `2` are adjacent. -/
theorem adj_C3_0_2 : (SimpleGraph.cycleGraph 3).Adj (0 : Fin 3) 2 := by
  decide

/-- In the full configuration `full3`, the open component of `0` is the whole
vertex set: every vertex is reachable from `0` by a path of open edges. -/
theorem component_C3_full :
    Component C3 full3 (0 : Fin 3) = Set.univ := by
  ext u
  constructor
  · intro _; trivial
  · intro _; unfold Component
    fin_cases u
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        (show openAdj C3 full3 (0 : Fin 3) 1 from by
          use adj_C3_0_1; simp [full3])
    · exact Relation.ReflTransGen.single
        (show openAdj C3 full3 (0 : Fin 3) 2 from by
          use adj_C3_0_2; simp [full3])

/-- The singleton `{0}` is **not** ω-closed in `full3`: the open edge `0—1`
leaves it. A component-closed set in the full configuration must be far larger
than a single vertex. -/
theorem not_openEdgeClosed_C3_singleton :
    ¬ openEdgeClosed C3 full3 ({0} : Set (Fin 3)) := by
  intro h
  have h1 : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) :=
    h (by simp) (show openAdj C3 full3 (0 : Fin 3) 1 from by
      use adj_C3_0_1; simp [full3])
  simp at h1

/-- The **boundary edge** of `{0}` in `full3`: the open edge `0—1` crosses from
`{0}` to its complement. This is the concrete witness that the complement of
`{0}` has a non-empty boundary — the boundary face of the kernel bridge. -/
theorem exists_boundary_edge_C3 :
    ∃ u v : Fin 3, u ∈ ({0} : Set (Fin 3)) ∧ v ∉ ({0} : Set (Fin 3)) ∧ openAdj C3 full3 u v := by
  refine ⟨(0 : Fin 3), (1 : Fin 3), ?_, ?_, ?_⟩
  · simp
  · simp
  · show openAdj C3 full3 (0 : Fin 3) 1
    use adj_C3_0_1; simp [full3]

/-- **Square** `C₄` — the 4-cycle. Unlike the triangle, `0` is not adjacent to
`2`: reaching it requires a two-edge path, hence the composition
`Relation.ReflTransGen.trans`. -/
abbrev C4 : SimpleGraph (Fin 4) := SimpleGraph.cycleGraph 4

/-- **Full configuration** on `C₄`: every edge is open. -/
abbrev full4 : Finset (Edge C4) := Finset.univ

/-- In the square `full4`, the open component of `0` reaches `2` through the
composition `0 — 1 — 2` (two edges), which **exercises** the `Relation.ReflTransGen.trans`
at the core of the tranche-3 kernel. Thus `component_C4_full` is the whole
vertex set. -/
theorem component_C4_full :
    Component C4 full4 (0 : Fin 4) = Set.univ := by
  ext u
  constructor
  · intro _; trivial
  · intro _; unfold Component
    fin_cases u
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        (show openAdj C4 full4 (0 : Fin 4) 1 from by
          use (by decide : (SimpleGraph.cycleGraph 4).Adj 0 1); simp [full4])
    · exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single
          (show openAdj C4 full4 (0 : Fin 4) 1 from by
            use (by decide : (SimpleGraph.cycleGraph 4).Adj 0 1); simp [full4]))
        (Relation.ReflTransGen.single
          (show openAdj C4 full4 (1 : Fin 4) 2 from by
            use (by decide : (SimpleGraph.cycleGraph 4).Adj 1 2); simp [full4]))
    · exact Relation.ReflTransGen.single
        (show openAdj C4 full4 (0 : Fin 4) 3 from by
          use (by decide : (SimpleGraph.cycleGraph 4).Adj 0 3); simp [full4])

/-- The singleton `{0}` is **not** ω-closed in `full4`: the open edge `0—1`
leaves it. -/
theorem not_openEdgeClosed_C4_singleton :
    ¬ openEdgeClosed C4 full4 ({0} : Set (Fin 4)) := by
  intro h
  have h1 : (1 : Fin 4) ∈ ({0} : Set (Fin 4)) :=
    h (by simp) (show openAdj C4 full4 (0 : Fin 4) 1 from by
      use (by decide : (SimpleGraph.cycleGraph 4).Adj 0 1); simp [full4])
  simp at h1

end Percolation_en

import Mathlib

/-!
# Astar.Graph — weighted graphs, paths, cost of a path

English mirror of `AStar/Graph.lean` (FR-first canonical), tranche 1 EPIC #4980
(astar_lean). Convention i18n Lean ratified by ai-01 (2026-07-04, #4980
comment-4881909354): distinct FR + EN sibling files in the same lake, both
compile; namespace `Astar_en` (anti-collision with FR `Astar`); non-docstring
content byte-identical (CI drift-detectable); EN docstrings manually translated.

Abstract model for the optimality proof of A* (issue #4048). A weighted directed
graph with non-negative edges (`NNReal` ≡ ℝ≥0), paths seen as lists of vertices,
and the cost of a path as the sum of the weights of its consecutive arcs.
-/

namespace Astar_en

/- Abstract vertices: `V` is the vertex type, a parameter of the model. -/
variable {V : Type*}

/-- Weighted directed graph: `edge a b` is the non-negative cost of the arc
    `a → b`. The value `0` means "no arc" (or a trivial loop). The
    non-negativity assumption (`NNReal`) is exactly the assumption required
    for the optimality of A*. -/
structure WeightedGraph (V : Type*) where
  /-- Weight (non-negative) of each directed arc. -/
  edge : V → V → NNReal

variable (G : WeightedGraph V)

/-- A path is a list of consecutive vertices. -/
abbrev Path (V : Type*) := List V

/-- Cost of a path = sum of the weights of the consecutive arcs.

    `pathCost [] = 0`, `pathCost [v] = 0` (a lone vertex has no arc),
    `pathCost [v₀, v₁, v₂, ...] = edge v₀ v₁ + edge v₁ v₂ + ...`. -/
def pathCost : Path V → NNReal
  | [] => 0
  | [_] => 0
  | v₀ :: v₁ :: rest => G.edge v₀ v₁ + pathCost (v₁ :: rest)

@[simp]
theorem pathCost_nil : pathCost G ([] : Path V) = 0 := rfl

@[simp]
theorem pathCost_singleton (v : V) : pathCost G [v] = 0 := rfl

@[simp]
theorem pathCost_cons_cons (v₀ v₁ : V) (rest : Path V) :
    pathCost G (v₀ :: v₁ :: rest) = G.edge v₀ v₁ + pathCost G (v₁ :: rest) := rfl

/-- A path `p` goes from `start` to `goal`: it is non-empty, its first vertex
    is `start` and its last vertex is `goal`. -/
def PathFrom (start goal : V) (p : Path V) : Prop :=
  p ≠ [] ∧ p.head? = some start ∧ p.getLast? = some goal

end Astar_en

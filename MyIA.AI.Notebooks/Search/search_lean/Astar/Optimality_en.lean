import Mathlib
import Astar.Graph
import Astar.Heuristic

/-!
# Astar.Optimality — f-bound (abstract lemma: suffix bound)

English mirror of `AStar/Optimality.lean` (FR-first canonical), tranche 3 EPIC #4980
(search_lean). Convention i18n Lean ratified by ai-01 (2026-07-04, #4980
comment-4881909354): distinct FR + EN sibling files in the same lake, both compile;
namespace `Astar_en` (anti-collision with FR `Astar`); non-docstring content
byte-identical (CI drift-detectable); EN docstrings manually translated.

Brick of the series (issue #4048, register #3801 — prong B "non-trivial problem").
We prove the **f-bound**: under an admissible heuristic, for any node `p.get i` of a
path `p` to the goal, `h(p.get i)` never exceeds the cost of the remaining suffix
`pathCost (p.drop i)`. This is the mathematical core of the A* optimality argument
(Hart, Nilsson & Raphael, 1968) — but **only that core**, in abstract form.

The lake does **not** model the A* algorithm (no priority queue, no closed set, no
returned path): there is therefore **no A* optimality theorem** here. The guarantee
"admissible heuristic ⇒ A* returns a path of optimal cost" — **false** for the
Graph-Search variant without re-opening (cf #14824) — is not proved.

`hStar` is a "true remaining optimal cost": the lower-bound property
`IsTrueRemainingCost` (the abstract form, cf #4048).
-/

namespace Astar_en

open Astar

variable {V : Type*} (G : WeightedGraph V)

/-! ## The "true remaining optimal cost" `hStar` -/

/-- `hStar` is a **lower bound** on the cost of any path going from its first vertex
    to the goal. This is the characteristic property of the true remaining optimal
    cost: for a finite graph, `hStar n = min { pathCost p | p goes from n to goal }`,
    a minimum attained (simple paths finite in number) and which therefore lower-
    bounds any realised path. We keep the abstract form (hypothesis) here, cleaner
    pedagogically (cf #4048). -/
def IsTrueRemainingCost (hStar : V → NNReal) (goal : V) : Prop :=
  ∀ (start : V) (p : Path V), PathFrom start goal p → hStar start ≤ pathCost G p

/-! ## Auxiliary lemma: a suffix of a path to the goal still goes to the goal -/

/-- If `p` goes from `start` to `goal`, then for any index `i`, the suffix `p.drop i`
    goes from `p.get i` to `goal`. -/
lemma suffix_pathFrom (p : Path V) (i : Fin p.length) (start goal : V)
    (hp : PathFrom start goal p) : PathFrom (p.get i) goal (p.drop i.val) := by
  obtain ⟨hnil, hhead, hlast⟩ := hp
  have hi : i.val < p.length := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · -- (p.drop i.val) ≠ []
    rw [Ne, List.drop_eq_nil_iff]
    omega
  · -- head? (p.drop i.val) = some (p.get i)
    rw [List.head?_drop, List.getElem?_eq_getElem hi]
    rfl
  · -- getLast? (p.drop i.val) = some goal
    have hne : ¬(p.length ≤ i.val) := by omega
    rw [List.getLast?_drop, if_neg hne]
    exact hlast

/-! ## Headline theorem: f-bound (suffix bound) -/

/-- **f-bound at the start.** Admissible heuristic + `hStar` lower bound ⇒
    `h(start) ≤ pathCost(p)` for any path `p` going to the goal from `start`.
    This is the f-bound (`f = g + h`) at the starting point. -/
theorem admissible_head_bound (h hStar : V → NNReal) (hAdm : Admissible h hStar)
    (goal start : V) (p : Path V) (hStar_lb : IsTrueRemainingCost G hStar goal)
    (hp : PathFrom start goal p) : h start ≤ pathCost G p :=
  le_trans (hAdm start) (hStar_lb start p hp)

/-- **f-bound on a suffix (admissible heuristic).** For any node `p.get i` of a path
    `p` to the goal, `h(p.get i) ≤ pathCost(p.drop i)`: the admissible heuristic
    value never exceeds the cost of the remaining suffix. This is the f-bound
    (`f = g + h`) at each node — the abstract core of the A* optimality argument
    (Hart, Nilsson & Raphael, 1968).

    **Scope — what this theorem does not say.** It bounds the heuristic by the
    suffix cost; it does **not** prove that A* returns a path of optimal cost. The
    lake models neither a priority queue, nor a closed set, nor a returned path:
    the guarantee "admissible heuristic ⇒ A* optimal" (false for the Graph-Search
    variant without re-opening, cf #14824) is not a theorem of this lake. -/
theorem admissible_le_suffix_cost (h hStar : V → NNReal) (hAdm : Admissible h hStar)
    (goal start : V) (p : Path V) (hStar_lb : IsTrueRemainingCost G hStar goal)
    (hp : PathFrom start goal p) (i : Fin p.length) :
    h (p.get i) ≤ pathCost G (p.drop i.val) := by
  apply le_trans (hAdm (p.get i))
  exact hStar_lb (p.get i) (p.drop i.val) (suffix_pathFrom p i start goal hp)



end Astar_en

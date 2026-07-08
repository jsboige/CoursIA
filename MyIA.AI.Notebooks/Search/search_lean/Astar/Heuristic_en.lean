import Mathlib
import Astar.Graph

/-!
# Astar.Heuristic — admissibility and consistency

English mirror of `AStar/Heuristic.lean` (FR-first canonical), tranche 2 EPIC #4980
(search_lean). Convention i18n Lean ratified by ai-01 (2026-07-04, #4980
comment-4881909354): distinct FR + EN sibling files in the same lake, both compile;
namespace `Astar_en` (anti-collision with FR `Astar`); non-docstring content
byte-identical (CI drift-detectable); EN docstrings manually translated.

Central definitions of A*. Let `hStar : V → NNReal` be the "true remaining optimal
cost" (the minimal cost to reach the goal from each vertex). A heuristic `h : V → NNReal`
is:

- **admissible** if `h n ≤ hStar n` for every vertex `n`: it never overestimates the
  remaining optimal cost;
- **consistent** (or monotone) if `h n ≤ edge n n' + h n'` for every arc `n → n'`:
  this is the "relaxation" of the Bellman equation (dynamic programming). Consistency
  implies admissibility (see `Optimality.lean`).

`hStar` remains abstract here; its characteristic property of lower-bounding the cost
of paths leading to the goal is stated in `Optimality.lean` (`IsTrueRemainingCost`).
For a finite graph, `hStar` is built as the minimum cost over the simple paths
reaching the goal (the minimum is attained, since simple paths are finite in number).
-/

namespace Astar_en

open Astar

variable {V : Type*} (G : WeightedGraph V)

/-- **Admissible** heuristic: never overestimates `hStar` (the true remaining optimal
    cost). Key assumption for the optimality of A*. -/
def Admissible (h hStar : V → NNReal) : Prop :=
  ∀ n : V, h n ≤ hStar n

/-- **Consistent** (monotone) heuristic: relaxation of the Bellman equation along
    each arc. Consistency implies admissibility (`consistent_implies_admissible`),
    and additionally guarantees that the function `f = g + h` is increasing along
    paths, so A* never re-expands a node. -/
def Consistent (h : V → NNReal) : Prop :=
  ∀ n n' : V, h n ≤ G.edge n n' + h n'

/-! ## Basic properties of the `Admissible` / `Consistent` predicates

Foundational companion lemmas (issue #4048): elementary properties of the two
central predicates. We notably establish the **connection to Dijkstra**: with the
zero heuristic `h ≡ 0`, A* reduces to Dijkstra's algorithm (uniform-cost search) —
a standard textbook fact (Russell & Norvig, §3.5). All proved 0 `sorry`. -/

/-- **Monotonicity of admissibility.** A heuristic bounded everywhere by an
    admissible heuristic is itself admissible. Reusable combinator: to "shave down"
    an overly optimistic heuristic while staying admissible. -/
theorem admissible_mono (h₁ h₂ hStar : V → NNReal) (hle : ∀ n, h₁ n ≤ h₂ n)
    (hadm : Admissible h₂ hStar) : Admissible h₁ hStar :=
  fun n => le_trans (hle n) (hadm n)

/-- **Closure under minimum.** The pointwise minimum of two admissible heuristics
    is admissible. This is the theoretical basis for combining heuristics: taking the
    `min` of several admissible heuristics preserves admissibility (and the optimality
    of A* that follows from it). -/
theorem admissible_min (h₁ h₂ hStar : V → NNReal) (hA : Admissible h₁ hStar)
    (_hB : Admissible h₂ hStar) : Admissible (fun n => min (h₁ n) (h₂ n)) hStar :=
  fun n => le_trans (min_le_left (h₁ n) (h₂ n)) (hA n)

/-- **The perfect heuristic is admissible.** The "true remaining optimal cost" `hStar`
    is itself admissible (upper bound of the set of admissible heuristics, in the sense
    that every admissible heuristic lower-bounds it). -/
theorem hStar_admissible (hStar : V → NNReal) : Admissible hStar hStar :=
  fun _ => le_rfl

/-- **Connection to Dijkstra (admissibility).** The zero heuristic `h ≡ 0` is
    admissible (`0 ≤ hStar` everywhere, trivial in `NNReal` ≡ ℝ≥0). A* with the zero
    heuristic reduces to uniform-cost search (Dijkstra). -/
theorem zero_admissible (hStar : V → NNReal) : Admissible (fun _ => (0 : NNReal)) hStar :=
  fun _ => zero_le

/-- **Connection to Dijkstra (consistency).** The zero heuristic `h ≡ 0` is consistent
    (`0 ≤ edge + 0` everywhere, trivial in `NNReal`). The companion of `zero_admissible`. -/
theorem zero_consistent : Consistent G (fun _ => (0 : NNReal)) :=
  fun _ _ => zero_le

end Astar_en

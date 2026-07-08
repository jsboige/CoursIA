import Mathlib
import Astar.Graph
import Astar.Heuristic
import Astar.Optimality

/-!
# Astar.Consistency — consistency ⟹ admissibility (telescoping)

English mirror of `AStar/Consistency.lean` (FR-first canonical), tranche 4 EPIC #4980
(search_lean). Convention i18n Lean ratified by ai-01 (2026-07-04, #4980
comment-4881909354): distinct FR + EN sibling files in the same lake, both compile;
namespace `Astar_en` (anti-collision with FR `Astar`); non-docstring content
byte-identical (CI drift-detectable); EN docstrings manually translated.

Issue #4048, target theorem `consistent_implies_admissible`. **Consistency**
(monotonicity per arc: `h n ≤ edge n n' + h n'`) is a **local** condition;
**admissibility** (`h n ≤ hStar n`) is a **global** condition. The bridge between
the two is a **telescoping**: along the arcs of a path `start = v₀ → v₁ → … → vₖ =
goal`, consistency composes into

```
h(start) ≤ edge(v₀,v₁) + h(v₁)
         ≤ edge(v₀,v₁) + edge(v₁,v₂) + h(v₂)
         ≤ …
         ≤ pathCost(p) + h(goal).
```

Under the natural assumption `h(goal) = 0` (the heuristic is zero at the goal), it
follows **`h(start) ≤ pathCost(p)` for any path `p` going to the goal** — this is
exactly the global bound that admissibility also provides (cf `admissible_head_bound`
in `Optimality.lean`). This is the substantive content of "consistency implies
admissibility": the local condition, by telescoping, attains the global bound for
free.

**Scoping note (honest).** In this abstract model, `hStar` is only a *lower bound*
on path costs (`IsTrueRemainingCost`), not necessarily the optimal cost realised.
Consistency gives `h(start) ≤ pathCost(p)` for **any** realised path `p`; deducing
`h(start) ≤ hStar(start)` would require `hStar` to be the *attained minimum*
(finite graph, finitely many simple paths). This "realisability of `hStar`" is
deliberately left abstract here (cf #4048: we prove the **abstract form**). The
result `consistent_implies_path_bound` below is therefore the **fully proven
substantive theorem**; it entails admissibility in the sense "never overestimates a
realised path cost", which is the exact optimality mechanism of A*. See Hart,
Nilsson & Raphael (1968).
-/

namespace Astar_en

open Astar

variable {V : Type*} (G : WeightedGraph V)

/-- **Consistency ⟹ path bound (telescoping).** Target theorem #4048
    (`consistent_implies_admissible`). A **consistent** heuristic that is zero at the
    goal (`h goal = 0`) never exceeds the cost of a realised path to the goal: for
    any path `p` from `start` to `goal`, `h(start) ≤ pathCost(p)`.

    Consistency is local (per arc); by telescoping along the arcs of the path, it
    attains the same global bound as admissibility (`h ≤ hStar ≤ pathCost`). This is
    the exact mechanism that makes A* optimal under a consistent heuristic: the
    function `f = g + h` is then increasing along paths, so no node is ever
    re-expanded (cf Hart, Nilsson & Raphael 1968). -/
theorem consistent_implies_path_bound (h : V → NNReal) (goal : V)
    (hCons : Consistent G h) (hGoal : h goal = 0)
    (start : V) (p : Path V) (hp : PathFrom start goal p) :
    h start ≤ pathCost G p := by
  obtain ⟨hnel, hhead, hlast⟩ := hp
  -- Auxiliary lemma: for any list `q` ending at `goal`, `h(q.head) ≤ pathCost q`.
  -- (We keep `start` abstract via its head position, to recurse on the tail.)
  have key : ∀ (q : Path V), q.getLast? = some goal →
      ∀ s : V, q.head? = some s → h s ≤ pathCost G q := by
    intro q
    induction q with
    | nil => simp
    | cons hd tl ih =>
      intro hqgoal s hs
      -- `hs : (hd :: tl).head? = some s`  ⟹  `hd = s`. (`subst` eliminates `s`, keeps `hd`.)
      have hhd : hd = s := by simp_all
      subst hhd
      cases tl with
      | nil =>
        -- `q = [hd]`, `getLast? = some goal` ⟹ `hd = goal`, then `pathCost = 0`.
        have hhdg : hd = goal := by simp_all
        simp only [pathCost_singleton]
        rw [hhdg, hGoal]
      | cons w rest' =>
        -- `q = hd :: w :: rest'`. The last vertex is carried by the tail.
        have hqgoal' : (w :: rest').getLast? = some goal := by simp_all
        -- Recurse on the tail `(w :: rest')`: `h w ≤ pathCost(w :: rest')`.
        have hihw : h w ≤ pathCost G (w :: rest') := ih hqgoal' w (by simp)
        -- Consistency at arc `(hd, w)`: `h hd ≤ edge(hd,w) + h w`.
        have hcons := hCons hd w
        -- `pathCost(hd :: w :: rest') = edge(hd,w) + pathCost(w :: rest')`.
        simp only [pathCost_cons_cons]
        linarith
  exact key p hlast start hhead

/-- **Consistency ⟹ admissibility in the path sense.** Immediate corollary of the
    telescoping: under a consistent heuristic zero at the goal, the heuristic at the
    start never exceeds the cost of a path leading to the goal — exactly the bound
    that admissibility provides (`admissible_head_bound`), attained here without any
    assumption on `hStar`. -/
theorem consistent_implies_admissible_bound (h : V → NNReal) (goal : V)
    (hCons : Consistent G h) (hGoal : h goal = 0)
    (start : V) (p : Path V) (hp : PathFrom start goal p) :
    h start ≤ pathCost G p :=
  consistent_implies_path_bound G h goal hCons hGoal start p hp

/-! ## Phase 3: monotonicity of `f = g + h` (no re-expansion) -/

/-- **Consistency ⟹ `f = g + h` monotone.** Target theorem #4048 phase 3
    (`consistent_implies_monotone_f`). Under a **consistent** heuristic, the
    evaluation function `f = g + h` (cost already traversed `g` + heuristic `h`) is
    **increasing** along expansions: if the cost already traversed progresses by the
    arc weight (`g n' = g n + edge n n'`), then `f` does not decrease (`f n ≤ f n'`).

    This is the exact mechanism that makes A* **efficient** under a consistent
    heuristic: the frontier of `f` never retreats, so **no node is ever re-expanded**.
    Compare with an admissible (but not consistent) heuristic, which guarantees
    optimality (phase 1) but allows re-expansions. The formalisation of
    "non-re-expansion" itself (modelling the priority queue) is left to phase 4
    (cf #4048) — we prove here the **central mathematical lemma**, which is its exact
    cause. See Hart, Nilsson & Raphael (1968).

    **Proof** (1 line): `g n' + h n' = g n + edge n n' + h n' ≥ g n + h n` by
    consistency (`h n ≤ edge n n' + h n'`), hence `linarith` after rewriting `g n'`.

    Abstraction note: `g` is left a parameter (not computed) — the result holds for
    any cost-already-traversed function satisfying the per-arc advancement relation,
    independently of the specific path taken to reach it. -/
theorem consistent_implies_f_monotone (h : V → NNReal)
    (hCons : Consistent G h)
    (g : V → NNReal) (n n' : V)
    (hg : g n' = g n + G.edge n n') :
    g n + h n ≤ g n' + h n' := by
  rw [hg]
  linarith [hCons n n']

end Astar_en

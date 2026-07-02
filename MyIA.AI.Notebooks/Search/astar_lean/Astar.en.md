# `astar_lean` — English documentation companion

> **Convention — issue #4980, user decision 2026-07-02 (option B).**
> The `.lean` source files (`lakefile.lean`, `Astar.lean`, `Astar/Graph.lean`,
> `Astar/Heuristic.lean`, `Astar/Optimality.lean`, `Astar/Consistency.lean`) are the
> **canonical French** documentation — the single source of truth, unchanged. This file
> is the **English companion**: a non-compiled Markdown mirror of the same docstrings,
> translated. It follows the `README.md` → `README.en.md` pattern of Epic #1650 (pilot:
> sudoku_lean #4998; rollout: finiteness #5000, kelly #5003, erc20 #5007, minimax #5008).
>
> - **Zero build cost** (Markdown is not compiled by `lake`), **zero risk** to
>   compilation — the `.lean` files are untouched.
> - **Source of truth = the `.lean`**. If the two ever disagree, the French in the
>   `.lean` wins; this companion mirrors the source and is regenerated against it.
>   Section order below matches declaration order in each file so drift is easy to spot.
> - Tactical `--` comments (inline, developer-facing, proof-tactic-bound) are
>   French-only in the source by convention and are **not** mirrored here — they are
>   tied to the Lean tactic language and add noise if duplicated.

---

## `lakefile.lean` — module

# Lean pedagogical mini-project: optimality of A*

A Lean 4 project (with Mathlib) formalizing the **flagship A* optimality theorem**: an
**admissible** heuristic guarantees that A* returns an optimal-cost path (Hart, Nilsson
& Raphael, 1968). See issue #4048 (roadmap #4038) and registry #3801 (prong B
"non-trivial problem" — answers the complaint "BFS vs A* degenerate" on a uniform-cost
graph, where the heuristic does not discriminate).

Approach: **abstract optimality lemma** (without modeling the full priority queue), as
suggested by #4048. Model: weighted graph with non-negative edges (`NNReal`), paths as
lists of vertices, admissible/consistent heuristic, `hStar` = the "true remaining optimal
cost" (a lower bound on the cost of paths leading to the goal).

Companion notebook (`Exploration_non_informée_et_informée_intro.ipynb`, Search series):
pedagogical presentation + the BFS-vs-A* counter-example on a weighted graph. Wiring the
notebook is the responsibility of the Search series owner.

(`Astar.lean` is four import lines — nothing to mirror.)

---

## `Astar/Graph.lean`

### Module

# Astar.Graph — weighted graphs, paths, cost of a path

Abstract model for the A* optimality proof (issue #4048). A weighted directed graph with
non-negative edges (`NNReal` ≡ ℝ≥0), paths seen as lists of vertices, and the cost of a
path as the sum of the weights of consecutive edges.

### `WeightedGraph`

Weighted directed graph: `edge a b` is the non-negative cost of the arc `a → b`. The
value `0` means "no edge" (or a trivial loop). The non-negativity assumption (`NNReal`)
is exactly the hypothesis required for A* optimality.

#### `WeightedGraph.edge`

Weight (non-negative) of each directed edge.

### `Path`

A path is a list of consecutive vertices.

### `pathCost`

Cost of a path = sum of the weights of consecutive edges.

`pathCost [] = 0`, `pathCost [v] = 0` (a lone vertex has no edge),
`pathCost [v₀, v₁, v₂, ...] = edge v₀ v₁ + edge v₁ v₂ + ...`.

### `pathCost_nil`, `pathCost_singleton`, `pathCost_cons_cons`

`@[simp]` computation lemmas for the empty path, the singleton, and the cons-cons case
(matching the three `pathCost` equations).

### `PathFrom`

A path `p` goes from `start` to `goal`: it is non-empty, its first vertex is `start`,
and its last vertex is `goal`.

---

## `Astar/Heuristic.lean`

### Module

# Astar.Heuristic — admissibility and consistency

Central definitions of A*. Let `hStar : V → NNReal` be the "true remaining optimal cost"
(the minimal cost to reach the goal from each vertex). A heuristic `h : V → NNReal` is:

- **admissible** if `h n ≤ hStar n` for every vertex `n`: it never overestimates the
  remaining optimal cost;
- **consistent** (or monotone) if `h n ≤ edge n n' + h n'` for every arc
  `n → n'`: this is the "relaxation" of the Bellman equation (dynamic programming).
  Consistency implies admissibility (see `Optimality.lean`).

`hStar` remains abstract here; its characteristic lower-bound property on the cost of
paths to the goal is stated in `Optimality.lean` (`IsTrueRemainingCost`). For a finite
graph, `hStar` is built as the minimum of the costs of simple paths to the goal (minimum
reached, since simple paths are finite in number).

### `Admissible`

**Admissible** heuristic: never overestimates `hStar` (the true remaining optimal cost).
Key hypothesis for A* optimality.

### `Consistent`

**Consistent** (monotone) heuristic: relaxation of the Bellman equation along each edge.
Consistency implies admissibility (`consistent_implies_admissible`), and further
guarantees that the function `f = g + h` is increasing along paths, so A* never
re-expands a node.

### Basic properties of the `Admissible` / `Consistent` predicates

Companion lemmas (issue #4048): elementary properties of the two central predicates.
Notably the **connection to Dijkstra**: with the zero heuristic `h ≡ 0`, A* reduces to
Dijkstra's algorithm (uniform-cost search) — a standard textbook fact (Russell & Norvig,
§3.5). All proven 0 `sorry`.

### `admissible_mono`

**Monotonicity of admissibility.** A heuristic everywhere upper-bounded by an admissible
heuristic is itself admissible. A reusable combinator: to "shave down" an overly
optimistic heuristic while keeping admissibility.

### `admissible_min`

**Closure under minimum.** The pointwise minimum of two admissible heuristics is
admissible. This is the theoretical basis for combining heuristics: taking the `min` of
several admissible heuristics preserves admissibility (and the A* optimality that
follows).

### `hStar_admissible`

**The perfect heuristic is admissible.** The "true remaining optimal cost" `hStar` is
itself admissible (upper bound of the set of admissible heuristics, in the sense that any
admissible one lower-bounds it).

### `zero_admissible`

**Connection to Dijkstra (admissibility).** The zero heuristic `h ≡ 0` is admissible
(`0 ≤ hStar` everywhere, trivial in `NNReal` ≡ ℝ≥0). A* with the zero heuristic reduces
to uniform-cost search (Dijkstra).

### `zero_consistent`

**Connection to Dijkstra (consistency).** The zero heuristic `h ≡ 0` is consistent
(`0 ≤ edge + 0` everywhere, trivial in `NNReal`). The companion of `zero_admissible`.

---

## `Astar/Optimality.lean`

### Module

# Astar.Optimality — admissible ⇒ optimal (abstract optimality lemma)

Flagship theorem of the series (issue #4048, registry #3801 — prong B "non-trivial
problem"). We prove the **`f`-bound** which is the exact mechanism of A* optimality:
under an admissible heuristic, `h(start)` never exceeds the cost of a path actually
reaching the goal. Applied to every suffix of the optimal path, this bound gives
`f(node) = g(node) + h(node) ≤ optimal cost` at every point of the optimal path — so A*
(which expands the node of minimal `f`) never crosses the optimal-cost frontier and
returns an optimal-cost path (Hart, Nilsson & Raphael, 1968).

We prove the **abstract form** (without modeling the full priority queue), as suggested
by #4048: `hStar` is a "true remaining optimal cost" satisfying the lower-bound property
`IsTrueRemainingCost`.

### `IsTrueRemainingCost`

`hStar` is a **lower bound** on the cost of any path going from its first vertex to the
goal. This is the characteristic property of the true remaining optimal cost: for a finite
graph, `hStar n = min { pathCost p | p goes from n to the goal }`, a minimum reached
(simple paths finite in number) and which therefore lower-bounds any realized path. We
keep the abstract form (hypothesis) here, cleaner pedagogically (cf #4048).

### `suffix_pathFrom`

Auxiliary lemma: if `p` goes from `start` to `goal`, then for any index `i`, the suffix
`p.drop i` goes from `p.get i` to `goal`.

### `admissible_head_bound`

**`f`-bound at the start.** Admissible heuristic + `hStar` lower bound ⇒ `h(start) ≤
pathCost(p)` for any path `p` reaching the goal from `start`. This is the `f`-bound
(`f = g + h`) at the start point.

### `admissible_implies_optimal`

**Admissible A* ⇒ optimal (abstract lemma).** Flagship theorem (issue #4048, registry
#3801).

Under an **admissible** heuristic, for any node `p.get i` of a path `p` reaching the
goal, the heuristic never exceeds the cost of the remaining suffix
`pathCost (p.drop i)`. This is the **`f`-bound** at every node: combined with
`f(node) = g(node) + h(node)` and the fact that `g + suffixCost = pathCost`, it gives
`f(node) ≤ pathCost(optimal)` along the optimal path — the exact optimality mechanism of
A* (expansion of the minimal `f` ⇒ the optimal-cost frontier is never crossed). See Hart,
Nilsson & Raphael (1968).

### `admissible_implies_optimal_start`

**Corollary: global bound at the start.** Special case `i = 0` (the start node):
`h(start) ≤ pathCost(p)`.

---

## `Astar/Consistency.lean`

### Module

# Astar.Consistency — consistency ⟹ admissibility (telescoping)

Issue #4048, target theorem `consistent_implies_admissible`. **Consistency**
(edge-monotonicity: `h n ≤ edge n n' + h n'`) is a **local** condition;
**admissibility** (`h n ≤ hStar n`) is a **global** condition. The bridge between the two
is a **telescoping**: along the edges of a path `start = v₀ → v₁ → … → vₖ = goal`,
consistency composes as

```
h(start) ≤ edge(v₀,v₁) + h(v₁)
         ≤ edge(v₀,v₁) + edge(v₁,v₂) + h(v₂)
         ≤ …
         ≤ pathCost(p) + h(goal).
```

Under the natural hypothesis `h(goal) = 0` (the heuristic is zero at the goal), it follows
that **`h(start) ≤ pathCost(p)` for every path `p` reaching the goal** — exactly the
global bound that admissibility also provides (cf `admissible_head_bound` in
`Optimality.lean`). This is the substantive content of "consistency implies admissibility":
the local condition, by telescoping, attains the global bound for free.

**Honest scoping note.** In this abstract model, `hStar` is only a *lower bound* on path
costs (`IsTrueRemainingCost`), not necessarily the realized optimal cost. Consistency
gives `h(start) ≤ pathCost(p)` for **any** realized path `p`; deducing
`h(start) ≤ hStar(start)` would require `hStar` to be the *reached minimum* (finite graph,
simple paths finite in number). This "`hStar` realizability" is deliberately left abstract
here (cf #4048: we prove the **abstract form**). The result `consistent_implies_path_bound`
below is thus the **fully proven substantive theorem**; it entails admissibility in the
sense "never overestimates a realized path cost", which is the exact A* optimality
mechanism. See Hart, Nilsson & Raphael (1968).

### `consistent_implies_path_bound`

**Consistency ⟹ path bound (telescoping).** Target theorem #4048
(`consistent_implies_admissible`). A **consistent** heuristic that is zero at the goal
(`h goal = 0`) never exceeds the cost of a realized path to the goal: for every path `p`
from `start` to `goal`, `h(start) ≤ pathCost(p)`.

Consistency is local (per edge); by telescoping along the path's edges, it attains the same
global bound as admissibility (`h ≤ hStar ≤ pathCost`). This is the exact mechanism that
makes A* optimal under a consistent heuristic: the function `f = g + h` is then increasing
along paths, so no node is ever re-expanded (cf Hart, Nilsson & Raphael 1968).

### `consistent_implies_admissible_bound`

**Consistency ⟹ admissibility in the path sense.** Immediate corollary of the telescoping:
under a consistent heuristic that is zero at the goal, the heuristic at the start never
exceeds the cost of a path leading to the goal — exactly the bound admissibility provides
(`admissible_head_bound`), attained here with no hypothesis on `hStar`.

### Phase 3: monotonicity of `f = g + h` (no re-expansion)

### `consistent_implies_f_monotone`

**Consistency ⟹ `f = g + h` monotone.** Target theorem #4048 phase 3
(`consistent_implies_monotone_f`). Under a **consistent** heuristic, the evaluation
function `f = g + h` (cost-so-far `g` + heuristic `h`) is **increasing** along expansions:
if the cost-so-far progresses by the edge weight (`g n' = g n + edge n n'`), then `f` does
not decrease (`f n ≤ f n'`).

This is the exact mechanism that makes A* **efficient** under a consistent heuristic: the
`f` frontier never retreats, so **no node is ever re-expanded**. Contrast with an
admissible (but non-consistent) heuristic, which guarantees optimality (phase 1) but
allows re-expansions. Formalizing "no-re-expansion" itself (modeling the priority queue)
is left to phase 4 (cf #4048) — we prove here the **central mathematical lemma**, which is
its exact cause. See Hart, Nilsson & Raphael (1968).

**Proof** (1 line): `g n' + h n' = g n + edge n n' + h n' ≥ g n + h n` by consistency
(`h n ≤ edge n n' + h n'`), hence `linarith` after rewriting `g n'`.

Abstraction note: `g` is left a parameter (not computed) — the result holds for any
cost-so-far function satisfying the edge-advancement relation, independently of the
specific path taken to reach it.

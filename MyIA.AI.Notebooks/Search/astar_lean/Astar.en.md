# Astar — English documentation companion

> **Convention.** This file is the **English translation of docstrings** in the
> `astar_lean` lake. It is a **non-compiled Markdown companion** to the Lean 4
> sources — the **French `.lean` source remains the single source of truth** and
> is unchanged. Tactical `--` comments inside proof bodies are **not** mirrored
> (they remain French-only, tactic-bound). Module docstrings (`/-! ... -/`) and
> per-declaration docstrings (`/-- ... -/`) are translated.
>
> Source lake: [`MyIA.AI.Notebooks/Search/astar_lean/`](./).
> Companion convention: PR #4980 rollout, option B (user decision 2026-07-02),
> pilot = PR #4998 (sudoku_lean). See #1650 (multilingual documentation EPIC).

---

## `lakefile.lean` — package manifest

**Module docstring (translated).**

A pedagogical Lean 4 project (with Mathlib) formalizing the **flagship A* optimality theorem**: an **admissible** heuristic guarantees that A* returns a path of optimal cost (Hart, Nilsson & Raphael, 1968). See issue #4048 (roadmap #4038) and register #3801 (prong B "non-trivial problem" — addresses the "BFS vs degenerate A*" complaint on uniform-cost graphs, where the heuristic does not discriminate).

Approach: **abstract optimality lemma** (without modeling the full priority queue), as suggested by #4048. Model: weighted directed graph with non-negative edges (`NNReal`), paths as lists of vertices, admissible/consistent heuristic, `hStar` = "true optimal remaining cost" (lower bound on the cost of paths leading to the goal).

Companion notebooks (`Search-2-Uninformed.ipynb` + `Search-3-Informed.ipynb`, Search series, Part1-Foundations): pedagogical presentation + BFS-vs-A* counter-example on a weighted graph. The historical `Exploration_non_informée_et_informée_intro.ipynb` (formerly at Search root, archived 2026-07-03 in `../archive/`) covered the same material in a single document. The notebook wiring belongs to the Search series owner.

---

## `Astar.lean` — top-level aggregator

A pure aggregator that re-exports the four sub-modules of the lake: `Astar.Graph`, `Astar.Heuristic`, `Astar.Optimality`, `Astar.Consistency`.

---

## `Astar/Graph.lean` — weighted graphs, paths, path cost

**Module docstring (translated).**

An abstract model for the A* optimality proof (issue #4048). A directed weighted graph with non-negative edges (`NNReal` ≡ ℝ≥0), paths viewed as lists of vertices, and the cost of a path as the sum of the weights of consecutive arcs.

### `WeightedGraph` — structure

A weighted directed graph: `edge a b` is the non-negative cost of the arc `a → b`. The value `0` means "no arc" (or a trivial loop). The non-negativity assumption (`NNReal`) is exactly the assumption required for A* optimality.

- **`edge : V → V → NNReal`** — (non-negative) weight of each directed arc.

### `Path` — abbrev

A path is a list of consecutive vertices.

### `pathCost` — definition

Cost of a path = sum of the weights of consecutive arcs.

    `pathCost [] = 0`, `pathCost [v] = 0` (a single vertex has no arc),
    `pathCost [v₀, v₁, v₂, ...] = edge v₀ v₁ + edge v₁ v₂ + ...`.

### `pathCost_nil` — theorem (`@[simp]`)

`pathCost G ([] : Path V) = 0`.

### `pathCost_singleton` — theorem (`@[simp]`)

`pathCost G [v] = 0`.

### `pathCost_cons_cons` — theorem (`@[simp]`)

`pathCost G (v₀ :: v₁ :: rest) = G.edge v₀ v₁ + pathCost G (v₁ :: rest)`.

### `PathFrom` — definition

A path `p` goes from `start` to `goal`: it is non-empty, its first vertex is `start`, and its last vertex is `goal`.

---

## `Astar/Heuristic.lean` — admissibility and consistency

**Module docstring (translated).**

Central definitions of A*. Let `hStar : V → NNReal` be the "true optimal remaining cost" (the minimal cost to reach the goal from each vertex). A heuristic `h : V → NNReal` is:

- **admissible** if `h n ≤ hStar n` for all vertices `n`: it never overestimates the optimal remaining cost;
- **consistent** (or monotone) if `h n ≤ edge n n' + h n'` for all arcs `n → n'`: this is the "relaxation" of the Bellman equation (dynamic programming). Consistency implies admissibility (see `Optimality.lean`).

`hStar` stays abstract here; its characteristic lower-bound property on the cost of paths leading to the goal is stated in `Optimality.lean` (`IsTrueRemainingCost`). For a finite graph, `hStar` is constructed as the minimum of the costs of simple paths leading to the goal (minimum attained, because simple paths are finite in number).

### `Admissible` — definition

**Admissible heuristic**: never overestimates `hStar` (the true optimal remaining cost). Key hypothesis for A* optimality.

### `Consistent` — definition

**Consistent** (monotone) **heuristic**: relaxation of the Bellman equation along each arc. Consistency implies admissibility (`consistent_implies_admissible`), and further guarantees that the function `f = g + h` is increasing along paths, hence A* never re-expands a node.

### Basic properties of `Admissible` / `Consistent`

Founding companion lemmas (issue #4048): elementary properties of the two central predicates. We notably establish the **connection to Dijkstra**: with the zero heuristic `h ≡ 0`, A* reduces to Dijkstra's algorithm (uniform-cost search) — a standard textbook fact (Russell & Norvig, §3.5). All proved 0 `sorry`.

### `admissible_mono` — theorem

**Monotonicity of admissibility.** A heuristic everywhere bounded above by an admissible heuristic is itself admissible. Reusable combinator: to "trim" an over-optimistic heuristic while staying admissible.

### `admissible_min` — theorem

**Closure under minimum.** The pointwise minimum of two admissible heuristics is admissible. This is the theoretical basis for heuristic combination: taking `min` of several admissible heuristics preserves admissibility (and the resulting A* optimality).

### `hStar_admissible` — theorem

**The perfect heuristic is admissible.** The "true optimal remaining cost" `hStar` is itself admissible (upper bound of the set of admissible heuristics, in the sense that every admissible heuristic underestimates it).

### `zero_admissible` — theorem

**Connection to Dijkstra (admissibility).** The zero heuristic `h ≡ 0` is admissible (`0 ≤ hStar` everywhere, trivial in `NNReal` ≡ ℝ≥0). A* with the zero heuristic reduces to uniform-cost search (Dijkstra).

### `zero_consistent` — theorem

**Connection to Dijkstra (consistency).** The zero heuristic `h ≡ 0` is consistent (`0 ≤ edge + 0` everywhere, trivial in `NNReal`). Companion to `zero_admissible`.

---

## `Astar/Optimality.lean` — admissible ⇒ optimal (abstract optimality lemma)

**Module docstring (translated).**

Flagship theorem of the series (issue #4048, register #3801 — prong B "non-trivial problem"). We prove the **f-bound** that is the exact optimality mechanism of A*: under an admissible heuristic, `h(start)` never exceeds the cost of a realized path to the goal. Applied to each suffix of the optimal path, this bound gives `f(node) = g(node) + h(node) ≤ optimal cost` at every point of the optimal path — hence A* (which deploys the node of minimal `f`) never crosses the optimal-cost frontier and returns a path of optimal cost (Hart, Nilsson & Raphael, 1968).

We prove the **abstract form** (without modeling the full priority queue), as suggested by #4048: `hStar` is a "true optimal remaining cost" satisfying the lower-bound property `IsTrueRemainingCost`.

### The "true optimal remaining cost" `hStar`

#### `IsTrueRemainingCost` — definition

`hStar` is a **lower bound** on the cost of any path going from its first vertex to the goal. This is the characteristic property of the true optimal remaining cost: for a finite graph, `hStar n = min { pathCost p | p goes from n to the goal }`, minimum attained (simple paths finite in number) and which therefore underestimates every realized path. We keep here the abstract form (hypothesis), pedagogically cleaner (cf #4048).

### Auxiliary lemma: a suffix of a goal-reaching path also reaches the goal

#### `suffix_pathFrom` — lemma

If `p` goes from `start` to `goal`, then for any index `i`, the suffix `p.drop i` goes from `p.get i` to `goal`.

### Flagship theorem: f-bound and optimality

#### `admissible_head_bound` — theorem

**f-bound at the start.** Admissible heuristic + `hStar` lower bound ⇒ `h(start) ≤ pathCost(p)` for every path `p` going to the goal from `start`. This is the f-bound (`f = g + h`) at the starting point.

#### `admissible_implies_optimal` — theorem

**A* admissible ⇒ optimal (abstract lemma).** Flagship theorem (issue #4048, register #3801).

Under an **admissible** heuristic, for every node `p.get i` of a path `p` going to the goal, the heuristic never exceeds the cost of the remaining suffix `pathCost (p.drop i)`. This is the **f-bound** at each node: combined with `f(node) = g(node) + h(node)` and the fact that `g + suffixCost = pathCost`, it gives `f(node) ≤ pathCost(optimal)` along the optimal path — the exact optimality mechanism of A* (deployment of the minimal `f` ⇒ the optimal-cost frontier is never crossed). See Hart, Nilsson & Raphael (1968).

#### `admissible_implies_optimal_start` — theorem

**Corollary: global bound at the start.** Special case `i = 0` (the starting node): `h(start) ≤ pathCost(p)`.

---

## `Astar/Consistency.lean` — consistency ⟹ admissibility (telescoping)

**Module docstring (translated).**

Issue #4048, target theorem `consistent_implies_admissible`. **Consistency** (monotonicity per arc: `h n ≤ edge n n' + h n'`) is a **local** condition; **admissibility** (`h n ≤ hStar n`) is a **global** condition. The bridge between the two is **telescoping**: along the arcs of a path `start = v₀ → v₁ → … → vₖ = goal`, consistency composes into

```
h(start) ≤ edge(v₀,v₁) + h(v₁)
         ≤ edge(v₀,v₁) + edge(v₁,v₂) + h(v₂)
         ≤ …
         ≤ pathCost(p) + h(goal).
```

Under the natural hypothesis `h(goal) = 0` (the heuristic vanishes at the goal), we get **`h(start) ≤ pathCost(p)` for every path `p` going to the goal** — exactly the global bound that admissibility also provides (cf `admissible_head_bound` in `Optimality.lean`). This is the substantial content of "consistency implies admissibility": the local condition, by telescoping, freely reaches the global bound.

**Honest framing note.** In this abstract model, `hStar` is only a *lower bound* on the costs of paths (`IsTrueRemainingCost`), not necessarily the realized optimal cost. Consistency gives `h(start) ≤ pathCost(p)` for **every** realized path `p`; deducing `h(start) ≤ hStar(start)` would require that `hStar` be the *attained minimum* (finite graph, simple paths finite in number). This "realizability of `hStar`" is deliberately left abstract here (cf #4048: we prove the **abstract form**). The result `consistent_implies_path_bound` below is therefore the **substantial theorem fully proved**; it implies admissibility in the sense "never overestimates a realized path cost", which is the exact optimality mechanism of A*. See Hart, Nilsson & Raphael (1968).

### `consistent_implies_path_bound` — theorem

**Consistency ⟹ path bound (telescoping).** Target theorem #4048 (`consistent_implies_admissible`). A **consistent** heuristic that vanishes at the goal (`h goal = 0`) never exceeds the cost of a realized path to the goal: for every path `p` from `start` to `goal`, `h(start) ≤ pathCost(p)`.

Consistency is local (per arc); by telescoping along the arcs of the path, it reaches the same global bound as admissibility (`h ≤ hStar ≤ pathCost`). This is the exact mechanism that makes A* optimal under a consistent heuristic: the function `f = g + h` is then increasing along paths, so no node is ever re-expanded (cf Hart, Nilsson & Raphael 1968).

### `consistent_implies_admissible_bound` — theorem

**Consistency ⟹ admissibility in the path sense.** Immediate corollary of the telescoping: under a consistent heuristic vanishing at the goal, the heuristic at the start never exceeds the cost of a path to the goal — exactly the bound provided by admissibility (`admissible_head_bound`), reached here without any hypothesis on `hStar`.

### Phase 3: monotonicity of `f = g + h` (no re-expansion)

#### `consistent_implies_f_monotone` — theorem

**Consistency ⟹ `f = g + h` monotone.** Target theorem #4048 phase 3 (`consistent_implies_monotone_f`). Under a **consistent** heuristic, the evaluation function `f = g + h` (cost already traversed `g` plus heuristic `h`) is **increasing** along expansions: if the cost already traversed progresses by the arc weight (`g n' = g n + edge n n'`), then `f` does not increase (`f n ≤ f n'`).

This is the exact mechanism that makes A* **efficient** under a consistent heuristic: the `f` frontier never retreats, so **no node is ever re-expanded**. To be compared with an admissible (but non-consistent) heuristic, which guarantees optimality (phase 1) but allows re-expansions. The formalization of "no re-expansion" itself (modeling the priority queue) is left to phase 4 (cf #4048) — we prove here the **central mathematical lemma**, which is its exact cause. See Hart, Nilsson & Raphael (1968).

**Proof** (1 line): `g n' + h n' = g n + edge n n' + h n' ≥ g n + h n` by consistency (`h n ≤ edge n n' + h n'`), hence `linarith` after rewriting `g n'`.

Abstraction note: `g` is left as a parameter (not computed) — the result holds for any already-traversed cost function satisfying the per-arc advancement relation, independently of the specific path taken to reach it.
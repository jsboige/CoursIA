# `planning_lean` — English documentation companion

> **Convention — issue #4980, user decision 2026-07-02 (option B).**
> The `.lean` source files (`lakefile.lean`, `Planning/Strips.lean`, `Planning/Relaxation.lean`,
> `Planning/Admissibility.lean`) are the **canonical French** documentation — the single
> source of truth, unchanged. This file is the **English companion**: a non-compiled
> Markdown mirror of the same docstrings, translated. It follows the `README.md` →
> `README.en.md` pattern of Epic #1650 (pilot: sudoku_lean #4998; rollout: finiteness
> #5000, kelly #5003, erc20 #5007, minimax #5008, astar #5014).
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

# Lean pedagogical mini-project: admissibility of the delete-relaxation (h⁺)

A Lean 4 project (with Mathlib) proving the **admissibility of the delete-relaxation** in
STRIPS planning: the relaxation ignores the *deletion* (`del`) effects of actions, which
makes reachability **monotone** (the state only grows). The fundamental result is

    h⁺ ≤ h*

where `h⁺` (resp. `h*`) is the cost of the optimal relaxed plan (resp. optimal real plan):
**every real plan is a relaxed plan**, so the minimum over relaxed plans is no greater than
the minimum over real plans. This admissibility formally justifies the relaxation
heuristics FF / h_add / h_max at the core of classical planning.

See issue #4053 (Lean roadmap #4038, Tier 2).

**Feasibility**: elementary combinatorics on `Finset`. The key lemma is
`step a s ⊆ stepR a s` (since `s \ a.del ⊆ s`), lifted to action sequences by induction on
the plan length via execution monotonicity. No dedicated infrastructure required in
Mathlib. The flagship theorem `relaxed_plan_admissible` is achievable **0 sorry**.

Companion notebook (`Planners` series): pedagogical presentation of relaxation heuristics
(h_max, h_add, FF). Sibling-lake convention: the lake is the formal deliverable, `lake
build` is the execution proof; wiring the companion notebook is the responsibility of the
Planners series owner.

---

## `Planning/Strips.lean`

### Module

# Planning.Strips — STRIPS model: fluents, states, actions, transitions

**STRIPS** (STanford Research Institute Problem Solver) is the canonical formalism of
classical planning. We model:

- a **fluent** (atomic fact) `F` as an arbitrary type (decidably equal, for set
  operations);
- a **state** `s : Finset F` as the set of true fluents;
- a STRIPS **action** `a = (pre, add, del)`:
  - `pre a`: preconditions (required fluents),
  - `add a`: add effects (fluents becoming true),
  - `del a`: *deletion* effects (fluents becoming false).

An action `a` is **applicable** in state `s` when `pre a ⊆ s`. The **real transition**
applies add AND del: `step a s = (s \ del a) ∪ add a`. The **relaxed transition**
(delete-free, core of h⁺) ignores deletions: `stepR a s = s ∪ add a`.

This relaxation makes reachability **monotone**: the relaxed state only grows, which makes
computing the relaxed plan polynomial and guarantees the **admissibility** h⁺ ≤ h*
(proven in `Admissibility.lean`). See issue #4053.

### `State`

A STRIPS **state** = the set of currently-true fluents.

### `Action`

A STRIPS **action**: preconditions, add effects, deletion effects.

#### `Action.pre`

Preconditions: fluents required for the action to be applicable.

#### `Action.add`

Add effects: fluents becoming true after the action.

#### `Action.del`

Deletion effects: fluents becoming false after the action (ignored by the relaxation).

### `applicable`

An action is **applicable** in `s` when its preconditions are satisfied.

### `step`

The **real transition**: remove deletions then add the adds.
`step a s = (s \ a.del) ∪ a.add`.

### `stepR`

The **relaxed transition** (delete-free): ignore deletions. `stepR a s = s ∪ a.add`. This
is the core of the h⁺ relaxation.

### `goalSatisfied`

The goal `g` is **satisfied** by state `s` when all the goal's fluents are present.

### `step_subset_stepR`

Key lemma: the real transition is included in the relaxed transition.
`step a s ⊆ stepR a s` because `s \ a.del ⊆ s`.

### `step_mono`

The real transition is **monotone** in the state: `s ⊆ s'` entails
`step a s ⊆ step a s'`.

### `stepR_mono`

The relaxed transition is **monotone** in the state: `s ⊆ s'` entails
`stepR a s ⊆ stepR a s'`.

---

## `Planning/Relaxation.lean`

### Module

# Planning.Relaxation — relaxed plan execution, monotone reachability

The **delete-relaxation** (h⁺) ignores the `del` effects of STRIPS actions:
`stepR a s = s ∪ a.add`. We define the **relaxed execution** `runR` of an action sequence
and the **real execution** `run` (which applies `del`).

The central fact is the **monotonicity of relaxed reachability**: a larger initial state
can only widen the reachable set (`runR_mono`). This monotonicity is what makes solving the
relaxed plan **polynomial** (increasing reachability → fixed-point computation in
polynomial time) and guarantees the admissibility h⁺ ≤ h* (proven in `Admissibility.lean`).
See issue #4053.

### `run`

**Real** execution of a plan (action sequence) from initial state `s`.

### `runR`

**Relaxed** (delete-free) execution of a plan from `s`.

### `reaches`

A plan `π` **reaches** goal `g` from `s` (real execution).

### `reachesR`

A plan `π` reaches `g` from `s` (relaxed execution).

### `run_mono`

Monotonicity of the real execution: `s ⊆ s'` entails `run π s ⊆ run π s'`.

### `runR_mono`

**Monotonicity of relaxed reachability**: `s ⊆ s'` entails `runR π s ⊆ runR π s'`. This is
what makes the relaxed-plan computation polynomial (increasing reachability).

### `run_subset_runR`

**Central lemma**: every real execution is included in the relaxed execution.
`run π s ⊆ runR π s`. Follows from `step ⊆ stepR` by induction on the plan length.

---

## `Planning/Admissibility.lean`

### Module

# Planning.Admissibility — h⁺ ≤ h*: the delete-relaxation is admissible

**Relaxation admissibility theorem**: the cost of the optimal relaxed plan `h⁺` never
exceeds the cost of the optimal real plan `h*`.

    h⁺ ≤ h*

The proof rests on the inclusion `run π s ⊆ runR π s` (every real plan is a relaxed plan):
since the relaxation ignores `del` effects, the relaxed state after applying an action
sequence always contains the corresponding real state. So any real plan reaching goal `g`
is also a relaxed plan reaching `g`. By optimality-minimality, the relaxed cost `h⁺` is no
greater than the real cost `h*`.

This result formally justifies the use of relaxation heuristics (h_max, h_add, FF) as
**admissible lower bounds** of the real cost — the foundation of modern planning.
See issue #4053 (roadmap Lean #4038, Tier 2).

#### Open milestone (not sorry-backed)

The **full h_max / h_add heuristic machinery** (fixed point of relaxed reachability, and
the inequality `h_max ≤ h⁺ ≤ h_add`) is not formalized here: it requires a recursive
definition of the relaxed-reachability fixed point and a convergence proof, which are
substantial. The fundamental admissibility `h⁺ ≤ h*` (the result that legitimizes the
entire relaxation-heuristic family) is proven 0 sorry below.

### `relaxed_plan_admissible`

**Relaxation admissibility theorem (h⁺ ≤ h*)**: every real plan reaching goal `g` is also
a relaxed plan reaching `g`. By optimality-minimality of costs, the relaxed cost `h⁺` is
therefore no greater than the real cost `h*`.

### `relaxed_plan_witness`

**Direct corollary**: if a real plan of length `n` reaches `g`, the same plan, executed in
relaxation, also reaches `g`. Operational formulation of h⁺ ≤ h* (there exists a relaxed
plan of cost ≤ every real plan, hence ≤ h*).

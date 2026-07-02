# Planning — English documentation companion

> **Convention.** This file is the **English translation of docstrings** in the
> `planning_lean` lake. It is a **non-compiled Markdown companion** to the Lean 4
> sources — the **French `.lean` source remains the single source of truth** and
> is unchanged. Tactical `--` comments inside proof bodies are **not** mirrored
> (they remain French-only, tactic-bound). Module docstrings (`/-! ... -/`) and
> per-declaration docstrings (`/-- ... -/`) are translated.
>
> Source lake: [`MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean/`](./).
> Companion convention: PR #4980 rollout, option B (user decision 2026-07-02),
> pilot = PR #4998 (sudoku_lean). See #1650 (multilingual documentation EPIC).

---

## `lakefile.lean` — package manifest

**Module docstring (translated).**

A pedagogical Lean 4 project (with Mathlib) proving the **admissibility of the delete-free relaxation** in STRIPS planning: the relaxation ignores the *deletion* effects (`del`) of the actions, which makes reachability **monotone** (the state can only grow). The fundamental result is

    h⁺ ≤ h*

where `h⁺` (resp. `h*`) is the cost of the optimal relaxed plan (resp. optimal real plan): **every real plan is a relaxed plan**, hence the minimum over relaxed plans is below the minimum over real plans. This admissibility formally justifies the FF / h_add / h_max relaxation heuristics at the heart of classical planning.

See issue #4053 (Lean roadmap #4038, Tier 2).

**Feasibility**: elementary combinatorics on `Finset`. The key lemma is `step a s ⊆ stepR a s` (because `s \ a.del ⊆ s`), lifted to action sequences by induction on plan length via execution monotonicity. No dedicated infrastructure required in Mathlib. The flagship theorem `relaxed_plan_admissible` is attainable at **0 sorry**.

Companion notebook (Planners series): pedagogical presentation of relaxation heuristics (h_max, h_add, FF). Sibling-lake conventions: the lake is the formal deliverable, the `lake build` is the proof of execution; the companion notebook wiring belongs to the Planners series owner.

---

## `Planning/Strips.lean` — STRIPS model: fluents, states, actions, transitions

**Module docstring (translated).**

**STRIPS** (STanford Research Institute Problem Solver) is the canonical formalism of classical planning. We model:

- a **fluent** (atomic fact) `F` as an arbitrary type (decidably equatable, for set operations);
- a **state** `s : Finset F` as the set of fluents that are currently true;
- a STRIPS **action** `a = (pre, add, del)`:
  - `pre a` : preconditions (fluents required),
  - `add a` : additive effects (fluents becoming true),
  - `del a` : *deletion* effects (fluents becoming false).

An action `a` is **applicable** in a state `s` when `pre a ⊆ s`. The **real transition** applies add AND del: `step a s = (s \ del a) ∪ add a`. The **relaxed transition** (delete-free, heart of h⁺) ignores the deletions: `stepR a s = s ∪ add a`.

This relaxation makes reachability **monotone**: the relaxed state only grows, which makes the relaxed-plan computation polynomial and guarantees the **admissibility** h⁺ ≤ h* (proved in `Admissibility.lean`). See issue #4053.

### `State` — abbrev

A STRIPS **state** = the set of fluents currently true.

### `Action` — structure

A STRIPS **action**: preconditions, additive effects, deletion effects.
- **`pre : Finset F`** — preconditions: fluents required for the action to be applicable.
- **`add : Finset F`** — additive effects: fluents becoming true after the action.
- **`del : Finset F`** — deletion effects: fluents becoming false after the action (ignored by the relaxation).

### `applicable` — definition

An action is **applicable** in `s` when its preconditions are satisfied.

### `step` — definition

The **real transition**: remove the deletions, then add the adds. `step a s = (s \ a.del) ∪ a.add`.

### `stepR` — definition

The **relaxed transition** (delete-free): ignore the deletions. `stepR a s = s ∪ a.add`. This is the heart of the h⁺ relaxation.

### `goalSatisfied` — definition

A goal `g` is **reached** by a state `s` when all fluents of the goal are present.

### `step_subset_stepR` — lemma

Key lemma: the real transition is included in the relaxed transition. `step a s ⊆ stepR a s` because `s \ a.del ⊆ s`.

### `step_mono` — lemma

The real transition is **monotone** in the state: `s ⊆ s'` implies `step a s ⊆ step a s'`.

### `stepR_mono` — lemma

The relaxed transition is **monotone** in the state: `s ⊆ s'` implies `stepR a s ⊆ stepR a s'`.

---

## `Planning/Relaxation.lean` — relaxed plan execution, monotone reachability

**Module docstring (translated).**

The **delete-free relaxation** (h⁺) ignores the `del` effects of STRIPS actions: `stepR a s = s ∪ a.add`. We define the **relaxed execution** `runR` of an action sequence and the **real execution** `run` (which applies `del`).

The central fact is the **monotonicity of relaxed reachability**: a larger initial state can only widen the reachable set (`runR_mono`). This monotonicity is what makes solving the relaxed plan **polynomial** (growing reachability → fixed-point computation in polynomial time) and guarantees the admissibility h⁺ ≤ h* (proved in `Admissibility.lean`). See issue #4053.

### `run` — definition

**Real execution** of a plan (action sequence) from the initial state `s`.

### `runR` — definition

**Relaxed execution** (delete-free) of a plan from `s`.

### `reaches` — definition

A plan `π` **reaches** the goal `g` from `s` (real execution).

### `reachesR` — definition

A plan `π` reaches `g` from `s` (relaxed execution).

### `run_mono` — lemma

Monotonicity of real execution: `s ⊆ s'` implies `run π s ⊆ run π s'`.

### `runR_mono` — theorem

**Monotonicity of relaxed reachability**: `s ⊆ s'` implies `runR π s ⊆ runR π s'`. This is what makes the relaxed-plan computation polynomial (growing reachability).

### `run_subset_runR` — theorem

**Central lemma**: every real execution is included in the relaxed execution. `run π s ⊆ runR π s`. Follows from `step ⊆ stepR` by induction on the length of the plan.

---

## `Planning/Admissibility.lean` — h⁺ ≤ h*: the delete-free relaxation is admissible

**Module docstring (translated).**

**Admissibility theorem of the relaxation**: the cost of the optimal relaxed plan `h⁺` never exceeds the cost of the optimal real plan `h*`.

    h⁺ ≤ h*

The proof relies on the inclusion `run π s ⊆ runR π s` (every real plan is a relaxed plan): since the relaxation ignores the `del` effects, the relaxed state after applying an action sequence always contains the corresponding real state. Hence every real plan reaching the goal `g` is also a relaxed plan reaching `g`. By minimality of the optimal cost, the relaxed cost `h⁺` is below the real cost `h*`.

This result formally justifies the use of relaxation heuristics (h_max, h_add, FF) as **admissible lower bounds** of the real cost — the foundation of modern planning. See issue #4053 (Lean roadmap #4038, Tier 2).

### Open milestone (not sorry-backed)

The **complete machinery of the h_max / h_add heuristics** (fixed point of relaxed reachability, and the inequality `h_max ≤ h⁺ ≤ h_add`) is not formalized here: it requires a recursive definition of the relaxed-reachability fixed point and the proof of convergence, which is substantial. The fundamental admissibility `h⁺ ≤ h*` (the result that legitimizes the whole family of relaxation heuristics) is proved at 0 sorry below.

### `relaxed_plan_admissible` — theorem

**Admissibility theorem of the relaxation (h⁺ ≤ h*)**: every real plan reaching the goal `g` is also a relaxed plan reaching `g`. By minimality of the optimal costs, the relaxed cost `h⁺` is therefore below the real cost `h*`.

### `relaxed_plan_witness` — theorem

**Direct corollary**: if a real plan of length `n` reaches `g`, the same plan, executed in the relaxation, also reaches `g`. Operational formulation of h⁺ ≤ h* (there exists a relaxed plan with cost ≤ any real plan, hence ≤ h*).
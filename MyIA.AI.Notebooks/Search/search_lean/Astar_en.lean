/-!
# Astar — root of the `search_lean` sub-lake (A* optimality)

English mirror of `Astar.lean` (FR-first canonical), root aggregator sibling
pair per EPIC #4980 (search_lean tranche). Convention i18n Lean ratified
by ai-01 (2026-07-04, #4980 comment-4881909354): distinct FR + EN sibling
files in the same lake, both compile; namespace `Astar_en` (anti-collision
with FR `Astar`); non-docstring content byte-identical (CI drift-detectable);
EN docstrings manually translated.

Aggregates the four bricks of the Lean 4 / Mathlib 4 formalization of
**A\* optimality under admissible heuristic** (Hart, Nilsson & Raphael,
1968).

## Sub-lake contents

- `Astar.Graph` — abstract model: weighted directed graph with non-negative
  edges (`NNReal`), paths seen as lists of vertices, cost of a path as the
  sum of the weights of its consecutive arcs.
- `Astar.Heuristic` — central definitions: heuristic `h : V → NNReal`,
  "true optimal remaining cost" `hStar`, conditions of **admissibility**
  (`h ≤ hStar`) and **consistency** (Bellman relaxation,
  `h n ≤ edge n n' + h n'`).
- `Astar.Optimality` — flagship theorem (register **#3801** prong B
  "non-trivial problem", see also **#4048** and roadmap **#4038**): under
  an admissible heuristic, the bound on `f = g + h` stays under the optimal
  cost at every point of an optimal path. Formalized as an **abstract
  optimality lemma**, without modelling the full priority queue.
- `Astar.Consistency` — bridge from locality to globality: **consistency**
  (local per-arc condition) **implies admissibility** (global per-path
  condition), by **telescoping** along the arcs.

## i18n convention #4980 (sibling pair)

The sub-lake follows the convention ratified on 2026-07-04 by ai-01:
**FR canonical + EN sibling `_en.lean` per module**, with distinct
namespaces (`Astar` ↔ `Astar_en`) to avoid any name collision. This file
(`Astar_en.lean`) is the strictly additive English mirror of the French
canonical root `Astar.lean`; both files share byte-identical imports in
the same order (drift-detectable by CI).

A markdown companion `Astar.en.md` complements the documentation with a
narrative English translation outside the compilation pipeline (option B
of #4980, piloted in `sudoku_lean` PR #4998).

## Companion notebooks

`Search/Part1-Foundations/` series:

- `Search-2-Uninformed.ipynb` — uninformed search (DFS, BFS, UCS) with a
  **BFS-vs-UCS counter-example** motivating A\*'s contribution.
- `Search-3-Informed.ipynb` — admissible / consistent heuristics and the
  optimality guarantee, in direct alignment with the proofs in
  `Astar.Optimality` and `Astar.Consistency`.
-/

import Astar.Graph
import Astar.Heuristic
import Astar.Optimality
import Astar.Consistency
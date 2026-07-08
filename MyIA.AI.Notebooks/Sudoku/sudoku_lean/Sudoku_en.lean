import Sudoku.Basic
import Sudoku.Propagation
import Sudoku.ExactCover

/-!
# Sudoku — soundness of propagation + exact-cover reduction (Lean 4)

Formalization of the **soundness of the propagation rules** of a Sudoku (naked
single, hidden single) and of the **Sudoku ⇔ exact cover reduction** (Knuth), the
formal foundation of the solvers taught in the `Sudoku` series (backtracking,
OR-Tools, .NET). See issue #4055 (Lean roadmap #4038).

## Contents
- `Sudoku.Basic`: abstract constraint structure — `Scopes` (all-distinct scopes),
  `Solution`, `IsSolution`, `AllDistinctOn`, `IsPeer`, `PresentIn`. The
  abstraction captures any "all-distinct-scopes" CSP (the 9×9 is an instance, not
  a special case).
- `Sudoku.Propagation`: the **keystone** `peer_excludes_value` (an assigned cell
  excludes its value from its peers) and the two soundness theorems
  `naked_single_sound` + `hidden_single_sound`, 0 `sorry`.
- `Sudoku.ExactCover`: the Sudoku ⇔ exact cover reduction (Knuth, 4-family encoding
  → 2 in the abstract framework). The capstone theorem `sudoku_iff_exact_cover`
  proves the **complete equivalence**: `solution_imp_exact_cover` (forward
  direction, via `toSelection` and the full-house lemma `full_house_present`) +
  `exact_cover_imp_solution` (reverse direction, via the inverse construction
  `fromSelection`), 0 `sorry`.

## Status
- Proved without `sorry`: (1) the soundness of the naked/hidden single rules
  (keystone `peer_excludes_value`, propagation removes no valid solution); (2) the
  **complete equivalence** Sudoku ⇔ exact cover — `(∃ σ, IsSolution scopes σ) ↔
  (∃ sel, IsExactCover sel scopes)` under the "full house" hypothesis (satisfied by
  the 9×9 where each scope has 9 cells for 9 values), in two steps: forward
  `solution_imp_exact_cover` + reverse `exact_cover_imp_solution`.
- Axioms: the standard Lean 4 kernel trio (`propext`, `Classical.choice`,
  `Quot.sound`) — `Classical.choice` is used for the non-constructive construction
  `fromSelection` (extracting a witness per cell from the `∃!` of cover). No ad-hoc
  axioms.
- Out of scope: the "17 minimum clues" result (massive computation, not
  formalizable).

## Cross-reference
- `Sudoku` series (C#/.NET + Python): the backtracking/OR-Tools/Infer.NET solvers
  whose propagation step this lake formally grounds.
- #2978 (Sudoku as a symbolic regex): the Lean angle there = `finiteness-derivatives`
  (recognizer termination), **no overlap** with the propagation/exact-cover
  formalized here (coordination verified).
-/

/-!
English mirror of `Sudoku.lean` (FR-first canonical), EPIC #4980 (i18n Lean).
Convention ratified 2026-07-04 (issue #4980): distinct FR + EN sibling files in the
same lake; this is a pure landing doc module (imports + module docstring, no
declarations) so no namespace suffix is needed (mirrors the FR root structure
exactly). Submodule EN siblings live under `Sudoku/*_en.lean` (#5538).
-/

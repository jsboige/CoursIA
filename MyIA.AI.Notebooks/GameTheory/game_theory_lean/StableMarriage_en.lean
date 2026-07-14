/-
  GameTheory.StableMarriage — root aggregator (EPIC #4365 phase 4)
  ================================================================

  This module groups together the 5 sub-modules absorbed from the former
  `stable_marriage_lean/StableMarriage/` (now removed):

  - `StableMarriage.Definitions`      (absorbed c.300)
  - `StableMarriage.GSState`          (c.301)
  - `StableMarriage.Lemmas`           (c.302/c.303)
  - `StableMarriage.GaleShapley`      (c.304)
  - `StableMarriage.Lattice`          (c.305)

  Removal of the `stable_marriage_lean/` checkout is effective
  (EPIC #4365 phase 4; anti-regression 4-step protocol respected:
  content entirely preserved here, lake build SUCCESS, 0 net `sorry`
  introduced). Prose/CI/inventory refs updated to game_theory_lean.

  i18n convention (EPIC #4980 ratified by user 2026-07-04): the
  sub-modules `.lean` and their `_en.lean` siblings (namespace
  `<Name>_en`) are auto-discovered by the lakefile's
  `globs := #[`StableMarriage.*]`. The CI drift-detection sees both languages.

  Convention i18n (EPIC #4980, user decision 2026-07-04): this file is the
  **English mirror** of the FR-canonical root aggregator `StableMarriage.lean`,
  following the **sibling pair model** ratified by user on 2026-07-04
  (see `code-style.md` §Lean i18n, line 35; Option B rejected: double cost +
  FR/EN drift + quality bias). The FR-canonical aggregator is byte-identical
  on the import block (root aggregator is imports-only); only the docstring
  differs between the two siblings.
-/

import StableMarriage.Definitions
import StableMarriage.Definitions_en
import StableMarriage.GSState
import StableMarriage.GSState_en
import StableMarriage.Lemmas
import StableMarriage.Lemmas_en
import StableMarriage.Lattice
import StableMarriage.Lattice_en
import StableMarriage.GaleShapley
import StableMarriage.GaleShapley_en

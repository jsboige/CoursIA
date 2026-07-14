/-
  Cooperative Game Theory Library
  ===============================

  A Lean 4 library for cooperative game theory, formalizing:
  - TU (Transferable Utility) Games
  - The Shapley Value and its axioms
  - The Core and stability concepts
  - Voting games and power indices

  Main Modules:
  - CooperativeGames.Basic: TUGame, coalitions, Core, convexity
  - CooperativeGames.Shapley: Shapley axioms, value, uniqueness

  References:
  - L.S. Shapley, "A Value for N-Person Games" (1953)
  - O. Bondareva, "Some applications of linear programming to cooperative games" (1963)
  - L.S. Shapley, "On balanced sets and cores" (1967)

  Convention i18n (EPIC #4980, user decision 2026-07-04): this file is the
  **English mirror** of the FR-canonical root aggregator `CooperativeGames.lean`,
  following the **sibling pair model** ratified by user on 2026-07-04
  (see `code-style.md` §Lean i18n, line 35; Option B rejected: double cost +
  FR/EN drift + quality bias). Substantive modules
  (`CooperativeGames.Basic_en`, `CooperativeGames.Shapley_en`, ...) live in
  sibling `_en.lean` files, auto-discovered by the lakefile `globs := #[...]`.
-/

import CooperativeGames.Basic_en
import CooperativeGames.Shapley_en
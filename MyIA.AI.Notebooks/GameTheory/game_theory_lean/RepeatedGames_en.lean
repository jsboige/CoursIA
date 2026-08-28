/-
  Repeated Games Library (EN mirror)
  ==================================

  Lean 4 formalization of the foundational results on infinitely repeated
  games with imperfect monitoring, companion formel of the pedagogical
  notebook GameTheory-6c (repeated games, prisoner's dilemma).

  ## Headline theorem

  `grim_trigger_sustains_iff`: cooperation yields at least as much value as a
  one-shot deviation followed by grim punishment iff the discount factor
  satisfies δ ≥ (T−R)/(T−P).

  This equivalence formalizes grim trigger's algebraic incentive condition.
  The module also proves that the punishment state is absorbing. It does not
  yet formalize the histories and strategy profiles required for a
  subgame-perfect Nash equilibrium.

  ## Structure

  - `RepeatedGames.Stage_en` — definitions of the stage game (PD with 4
    parameters T > R > P > S, 2R > T + S), actions {C, D}, payoffs.
  - `RepeatedGames.Discounting_en` — discount factor, geometric sums for
    the R, T + δ·P discounted flows. Threshold rewrite lemma (prover BG
    target).
  - `RepeatedGames.GrimTrigger_en` — grim transition (punishment is absorbing)
    and the discounted-stream incentive condition `grim_trigger_sustains_iff`.
    Complete strategy/SPNE semantics remain outside this module.
  - `RepeatedGames.Folk_en` (STRETCH) — discounted Folk theorem (Fudenberg–
    Maskin 1986), `sorry` accepted within the companion's stretch scope.

  ## Mutualized lake cohort

  Toolchain `leanprover/lean4:v4.31.0-rc1`, Mathlib rev `d568c8c0` —
  consistent with 18 other lakes (see `.claude/rules/lean-merge-discipline.md`
  + `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/RUNBOOK.md`).
  Shared cache junction `.lake/packages/mathlib4` (see Issue #4363) —
  zero fresh Mathlib physical checkouts.

  Reference: GameTheory-6c notebook (repeated games, theory and numerics).

  i18n convention (EPIC #4980 ratified by user 2026-07-04): the
  sub-modules `_en.lean` (namespace `RepeatedGames_en`) are auto-discovered
  by the lakefile's `globs := #[`RepeatedGames.*]`. The CI drift-detection
  sees both languages.

  Convention i18n (EPIC #4980, user decision 2026-07-04): this file is the
  **English mirror** of the FR-canonical root aggregator `RepeatedGames.lean`,
  following the **sibling pair model** ratified by user on 2026-07-04
  (see `code-style.md` §Lean i18n, line 35; Option B rejected: double cost +
  FR/EN drift + quality bias). The FR-canonical aggregator is byte-identical
  on the import block (root aggregator is imports-only); only the docstring
  differs between the two siblings.
-/

import RepeatedGames.Stage_en
import RepeatedGames.Discounting_en
import RepeatedGames.GrimTrigger_en
import RepeatedGames.Folk_en

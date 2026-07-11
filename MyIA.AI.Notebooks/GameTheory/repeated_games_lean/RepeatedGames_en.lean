/-
  Repeated Games Library
  ======================

  Lean 4 formalization of the foundational results on infinitely repeated
  games with imperfect monitoring, companion formel of the pedagogical
  notebook GameTheory-6c (repeated games, prisoner's dilemma).

  ## Headline theorem

  `grim_trigger_sustains_iff`: the grim-trigger strategy sustains
  cooperation iff the discount factor satisfies δ ≥ (T−R)/(T−P).

  This inequality characterizes the threshold below which a player prefers
  to deviate (gain T today then endure P forever) rather than cooperate
  perpetually (R forever). The mechanism is the one-shot deviation
  principle (Lemke–Tarski): no deviation over two periods or more beats
  the deviation in a single period, so looking at the one-shot trade-off
  is sufficient.

  ## Structure

  - `RepeatedGames.Stage` — definitions of the stage game (PD with 4
    parameters T > R > P > S, 2R > T + S), actions {C, D}, payoffs.
  - `RepeatedGames.Discounting` — discount factor, geometric sums for
    the R, T + δ·P discounted flows. Threshold rewrite lemma (prover BG
    target).
  - `RepeatedGames.GrimTrigger` — grim strategy (cooperate → if deviation
    detected, eternal defection), headline theorem `grim_trigger_sustains_iff`,
    NE corollary. These two sorries are the prover BG primary targets.
  - `RepeatedGames.Folk` (STRETCH) — discounted Folk theorem (Fudenberg–
    Maskin 1986), `sorry` accepted within the companion's stretch scope.

  ## Mutualized lake cohort

  Toolchain `leanprover/lean4:v4.31.0-rc1`, Mathlib rev `d568c8c0` —
  consistent with 18 other lakes (see `.claude/rules/lean-merge-discipline.md`
  + `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/RUNBOOK.md`).
  Shared cache junction `.lake/packages/mathlib4` (see Issue #4363) —
  zero fresh Mathlib physical checkouts.

  Reference: GameTheory-6c notebook (repeated games, theory and numerics).

  Convention i18n (EPIC #4980, user decision 2026-07-04): this file is the
  **English mirror** of the FR-canonical root aggregator `RepeatedGames.lean`,
  following the **sibling pair model** ratified by user on 2026-07-04
  (see `code-style.md` §Lean i18n, line 35; Option B rejected: double cost +
  FR/EN drift + quality bias). Substantive modules (`RepeatedGames.Stage_en`,
  `RepeatedGames.Discounting_en`, `RepeatedGames.GrimTrigger_en`,
  `RepeatedGames.Folk_en`) live in sibling `_en.lean` files, auto-discovered
  by the lakefile `globs := #[`RepeatedGames.*]`.
-/

import RepeatedGames.Stage_en
import RepeatedGames.Discounting_en
import RepeatedGames.GrimTrigger_en
import RepeatedGames.Folk_en
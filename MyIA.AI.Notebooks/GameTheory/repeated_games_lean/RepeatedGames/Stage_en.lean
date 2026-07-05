import Mathlib.Tactic

/-
  Stage Game: the Prisoner's Dilemma (EN sibling)
  ==============================================

  English mirror of `RepeatedGames/Stage.lean` (FR-first canonical,
  tranche 14 EPIC #4980). Convention i18n Lean ratified by ai-01
  (2026-07-04, issue #4980 comment-4881909354): for each FR-canonical
  `Foo.lean`, a sibling `Foo_en.lean` preserves the EN verbatim in the
  `_en` namespace to
  (a) allow both to compile in the same lake,
  (b) detect CI drift between FR and EN on non-docstring content,
  (c) keep the EN version as a pedagogical reference.

  Namespace: `RepeatedGames_en` (anti-collision with `RepeatedGames` of
  the FR canonical `Stage.lean`). External access:
  `RepeatedGames_en.PDAction`, `RepeatedGames_en.PrisonersDilemma`, etc.
  No external module imports this EN sibling; the FR-canonical modules
  (Discounting, GrimTrigger, Folk) reference `RepeatedGames.PrisonersDilemma`
  via `open RepeatedGames` (the FR namespace), and the higher-level EN
  siblings (Discounting_en, GrimTrigger_en) likewise reference the FR
  base types. This Stage_en is the autonomous EN mirror of the foundation.

  Methodological note: manual translation of the FR canonical (no historical
  pre-Option-A EN source to recover; FR-first file since origin).
-/

/-!
# Stage Game: the Prisoner's Dilemma

We formalise the underlying stage game: the Prisoner's Dilemma,
parameterised by four reals `T, R, P, S` satisfying the standard
constraints `T > R > P > S` and `2 * R > T + S`.

Notation (Gibbons 1992):
  - `T` (Temptation): payoff of a unilateral deviation against a cooperator,
  - `R` (Reward)    : payoff of mutual cooperation,
  - `P` (Punishment): payoff of mutual defection,
  - `S` (Sucker)    : payoff of the exploited cooperator.

The constraint `2 * R > T + S` guarantees that mutual cooperation
Pareto-dominates the alternate exploit/be-exploited pattern.
-/

namespace RepeatedGames_en

/-- A player's action: Cooperate or Defect. -/
inductive PDAction where
  | cooperate : PDAction
  | defect : PDAction
  deriving DecidableEq, Repr

open PDAction

/-- Parameters of the Prisoner's Dilemma. The structure carries the
constraints `T > R > P > S` and `2 * R > T + S` as proof fields, so that
no implicit hypothesis is needed downstream. -/
structure PrisonersDilemma where
  (T R P S : ℝ)
  (hTR : T > R)
  (hRP : R > P)
  (hPS : P > S)
  (hPD : 2 * R > T + S)

/-- Stage payoff for the reference player (row) against the opponent's
move `b`. Standard payoff matrix:

    b = cooperate  |  b = defect
  C :   R          |  S
  D :   T          |  P
-/
def stagePayoff (g : PrisonersDilemma) (a b : PDAction) : ℝ :=
  match a, b with
  | cooperate, cooperate => g.R
  | defect,    cooperate => g.T
  | cooperate, defect    => g.S
  | defect,    defect    => g.P

/-- In a PD, defecting strictly dominates cooperating whatever the
opponent's move: `T > R` (opponent cooperates) and `P > S` (opponent
defects). This is precisely what makes cooperation irrational in the
*one-shot* game - and therefore non-trivial to sustain in the repeated game. -/
lemma defect_strictly_dominates (g : PrisonersDilemma) (b : PDAction) :
    stagePayoff g defect b > stagePayoff g cooperate b := by
  cases b
  · simp only [stagePayoff]; exact g.hTR
  · simp only [stagePayoff]; exact g.hPS

/-- Mutual cooperation Pareto-dominates mutual defection (`R > P`). -/
lemma mutual_coop_better_than_mutual_defect (g : PrisonersDilemma) :
    g.R > g.P := g.hRP

/-- The deviation payoff `T` is strictly greater than `R`. -/
lemma temptation_gt_reward (g : PrisonersDilemma) : g.T > g.R := g.hTR

end RepeatedGames_en

import Mathlib.Tactic

import RepeatedGames.Stage
import RepeatedGames.Discounting_en

/-!
  Grim Trigger — flagship theorem (EN sibling)
  =============================================

  English mirror of `RepeatedGames/GrimTrigger.lean` (FR-first canonical).
  Convention i18n Lean ratifiée par ai-01 (2026-07-04, #4980 comment-4881909354) :
  fichiers `.lean` distincts FR + EN siblings dans le même lake, les deux compilent.
  Drift-CI detectable : contenu non-docstring byte-identique entre siblings.

  Note méthodologique : traduction manuelle du FR canonique (pas de source
  EN historique pré-Option A à recover, fichier FR-first depuis origin).

  This module formalizes two building blocks of grim trigger in the
  infinitely repeated Prisoner's Dilemma:

  1. the irreversible transition to punishment after the first defection;
  2. the algebraic equivalence between no gain from a one-shot deviation and
     the threshold `δ ≥ (T − R) / (T − P)`.

  The second building block is the incentive condition used by the classical
  one-shot deviation argument. By itself, it is not a formalization of a
  subgame-perfect Nash equilibrium: that requires semantics for histories
  and strategy profiles.

  **Companion notebook**: `GameTheory-6c` (repeated games) derives this
  threshold by hand. Bridge `ICT-13` (#4879): the numerical verification of
  threshold δ is a gate.
-/

namespace RepeatedGames_en

open RepeatedGames
open PDAction

/-! ## Grim trigger strategy -/

/-- Grim-trigger transition. `prevSelf` encodes the current state:
`defect` means that punishment has already started. That state is absorbing;
otherwise, the foe's first defection triggers punishment. -/
def grimNext (prevSelf prevFoe : PDAction) : PDAction :=
  match prevSelf, prevFoe with
  | defect, _ => defect
  | cooperate, cooperate => cooperate
  | cooperate, defect => defect

@[simp]
theorem grimNext_cooperate_cooperate :
    grimNext cooperate cooperate = cooperate := rfl

@[simp]
theorem grimNext_cooperate_defect :
    grimNext cooperate defect = defect := rfl

@[simp]
theorem grimNext_defect_cooperate :
    grimNext defect cooperate = defect := rfl

@[simp]
theorem grimNext_defect_defect :
    grimNext defect defect = defect := rfl

/-- Once punishment has been triggered, it remains active regardless of the
foe's next move. -/
theorem grimPunishment_absorbing (prevFoe : PDAction) :
    grimNext defect prevFoe = defect := by
  cases prevFoe <;> rfl

/-! ## One-shot deviation incentive condition -/

/-- **Cooperation dominates a one-shot deviation iff
`δ ≥ (T − R) / (T − P)`.**

This equivalence compares the two discounted streams associated with the
cooperative path and a deviation followed by grim punishment. It establishes
the algebraic incentive condition used by the one-shot deviation principle;
it does not yet quantify over the histories or strategy profiles required by
a formal SPNE statement.

By `coop_ge_deviate_iff`, this result reduces to the explicit threshold on
`δ`. -/
theorem grim_trigger_sustains_iff (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) :
    (coopValue g.R δ ≥ deviateValue g.T g.P δ) ↔
      δ ≥ (g.T - g.R) / (g.T - g.P) := by
  exact coop_ge_deviate_iff g h0 h1

end RepeatedGames_en

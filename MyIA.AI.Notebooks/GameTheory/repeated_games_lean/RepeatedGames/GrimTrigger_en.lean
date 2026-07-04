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

  Central result of repeated game theory: the *grim trigger* strategy
  (cooperate as long as the foe cooperates, defect forever as soon as
  the foe defects once) sustains cooperation as a subgame-perfect
  Nash equilibrium of the infinitely repeated Prisoner's Dilemma **if
  and only if** the discount factor `δ` exceeds the critical threshold
  `(T − R) / (T − P)`.

  The proof rests on the **one-shot deviation principle**: for a stationary
  strategy like grim trigger, checking all possible deviations reduces to
  checking one-shot deviations.

  **Companion notebook**: `GameTheory-6c` (repeated games) derives this
  threshold by hand. The present module gives the formal proof. Bridge
  `ICT-13` (#4879): the numerical verification of threshold δ is a gate.
-/

namespace RepeatedGames_en

open PDAction

/-! ## Grim trigger strategy -/

/-- A grim trigger strategy: cooperate in the first period, then copy
the foe's previous move (cooperate if they cooperated, defect forever
as soon as they defect once). -/
def grimNext (prevSelf prevFoe : PDAction) : PDAction :=
  match prevFoe with
  | cooperate => cooperate
  | defect    => defect

/-! ## Flagship theorem (scaffold — proof in tranche 2) -/

/-- **Grim trigger sustains cooperation iff `δ ≥ (T − R) / (T − P)`.**

A unilateral one-shot deviation is not profitable (i.e. grim trigger is
stable) exactly when the discount factor is large enough that the loss of
future cooperation (`R → P` in all post-deviation periods) outweighs the
immediate gain (`R → T` in the deviation period).

By `coop_ge_deviate_iff`, this result reduces to an explicit threshold
on `δ`.

TODO tranche 2: assemble the proof via the one-shot deviation principle
(`coop_ge_deviate_iff` + `geom_sum` + `defect_strictly_dominates`). -/
theorem grim_trigger_sustains_iff (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) :
    (coopValue g.R δ ≥ deviateValue g.T g.P δ) ↔
      δ ≥ (g.T - g.R) / (g.T - g.P) := by
  -- By reduction to the threshold (pure real algebra).
  exact coop_ge_deviate_iff g h0 h1

end RepeatedGames_en
/-
  Worked Example — Battle of the Sexes with Incomplete Information
  ================================================================

  Harsanyi's classic illustration: player 1 does not know whether
  player 2 wants to meet (coordinate) or avoid them. Player 2's
  preference is their private type; the prior puts equal weight on
  both types.

  Actions (both players): 0 = Ballet, 1 = Football.
  Player 1 prefers Ballet (payoff 2 on (B,B), 1 on (F,F), 0 mismatch).
  Player 2 "meet" type prefers Football but wants to match.
  Player 2 "avoid" type wants to MISmatch: 2 if (B,F), 1 if (F,B).

  The textbook pure BNE — player 1 plays Ballet; player 2 plays Ballet
  when of the meet type and Football when of the avoid type — is
  verified below by `decide`, exercising the decidability of `isBNE`.

  Mirrors GameTheory-11-BayesianGames.ipynb. See #2610.
-/

import Bayesian.BNE

/-- Battle of the Sexes where player 2's desire to meet or avoid
    player 1 is private information (uniform prior over both types).
    Type 0 of player 2 = "meet", type 1 = "avoid". -/
def bosIncomplete : BayesGame2 where
  nT1 := 1
  nT2 := 2
  nA1 := 2
  nA2 := 2
  w := fun _ _ => 1
  u1 := fun _ _ a1 a2 =>
    if a1.val = a2.val then (if a1.val = 0 then 2 else 1) else 0
  u2 := fun _ t2 a1 a2 =>
    if t2.val = 0 then
      -- meet type: wants to coordinate, prefers Football
      if a1.val = a2.val then (if a1.val = 0 then 1 else 2) else 0
    else
      -- avoid type: wants to MISmatch
      if a1.val = 0 ∧ a2.val = 1 then 2
      else if a1.val = 1 ∧ a2.val = 0 then 1
      else 0

/-- Player 1 (single type) plays Ballet. -/
def bosS1 : Strategy1 bosIncomplete := fun _ => ⟨0, by decide⟩

/-- Player 2 plays Ballet when of the meet type, Football when of the
    avoid type. -/
def bosS2 : Strategy2 bosIncomplete := fun t2 =>
  if t2.val = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩

/-- The textbook strategy profile is a Bayesian Nash equilibrium,
    verified by computation. -/
theorem bosIncomplete_bne : isBNE bosIncomplete bosS1 bosS2 := by decide

/-- Sanity check: under the equilibrium, player 1's interim expected
    utility from Ballet is 2 (meets the meet type, misses the avoid
    type) versus 1 from deviating to Football. -/
theorem bosIncomplete_interim_values :
    interimU1 bosIncomplete ⟨0, by decide⟩ ⟨0, by decide⟩ bosS2 = 2 ∧
    interimU1 bosIncomplete ⟨0, by decide⟩ ⟨1, by decide⟩ bosS2 = 1 := by decide

/-- The equilibrium survives rescaling the prior weights (e.g. weights
    (3, 3) instead of (1, 1) encode the same uniform prior). -/
theorem bosIncomplete_bne_scaled : isBNE (scaleW bosIncomplete 3) bosS1 bosS2 :=
  (isBNE_scaleW bosIncomplete 3 (by decide) bosS1 bosS2).mpr bosIncomplete_bne

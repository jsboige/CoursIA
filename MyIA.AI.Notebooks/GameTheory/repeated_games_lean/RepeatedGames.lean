/-
  Repeated Games Library
  ======================

  A Lean 4 library for repeated game theory, formalizing the classical
  result that grim trigger sustains cooperation in the infinitely repeated
  Prisoner's Dilemma if and only if the discount factor is large enough:

    grim_trigger_sustains_iff : (no profitable one-shot deviation) ↔ δ ≥ (T−R)/(T−P)

  The proof rests on the one-shot deviation principle and geometric series
  (Mathlib `tsum_geometric_of_lt_one`).

  Main Modules:
  - RepeatedGames.Stage: the stage game (Prisoner's Dilemma parameters,
    action profiles, stage payoffs)
  - RepeatedGames.Discounting: discounted payoff streams, geometric sums
  - RepeatedGames.GrimTrigger: the theorem phare (one-shot deviation principle)

  Companion notebook: GameTheory-6c (jeux répétés) — the lake is the formal
  counterpart deriving the central threshold result rigorously.

  References:
  - R. Gibbons, "Game Theory for Applied Economists" (1992), ch. 2
  - D. Fudenberg and J. Tirole, "Game Theory" (1991), ch. 5
  - Pont ICT-13 (#4879): numerical verification of the δ threshold is a gate there.
-/

import RepeatedGames.Stage
import RepeatedGames.Discounting
import RepeatedGames.GrimTrigger

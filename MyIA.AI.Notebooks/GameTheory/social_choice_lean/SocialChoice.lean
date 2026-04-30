/-
  Social Choice Theory Library
  ============================

  Lean 4 formalizations inspired by asouther4/lean-social-choice (Lean 3)
  and chasenorman/Formalized-Voting (Lean 4).

  Arrow's proof follows the Geanakoplos 2005 approach.
  Sen's liberal paradox uses a bidirectional formulation (Sen 1970).
  Voting.lean adds margin-based definitions, Condorcet criteria,
  single-peaked preferences, Split Cycle, and clone-proofness.

  Arrow.lean and Sen.lean: FORMAL-CERTIFIED (0 sorry).
  Voting.lean: FORMAL-SKETCH (3 sorry in median_voter_theorem).

  Reference: Amartya Sen, "Collective Choice and Social Welfare" (1970)
  Reference: John Geanakoplos, "Three Brief Proofs of Arrow's Impossibility Theorem" (2005)

  Original Lean 3 repository:
  https://github.com/asouther4/lean-social-choice

  Lean 4 reference (DominikPeters):
  https://github.com/DominikPeters/SocialChoiceLean
-/

import SocialChoice.Basic
import SocialChoice.Framework
import SocialChoice.Arrow
import SocialChoice.Sen
import SocialChoice.Voting

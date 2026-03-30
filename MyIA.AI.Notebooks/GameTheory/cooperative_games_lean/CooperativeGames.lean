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
-/

import CooperativeGames.Basic
import CooperativeGames.Shapley

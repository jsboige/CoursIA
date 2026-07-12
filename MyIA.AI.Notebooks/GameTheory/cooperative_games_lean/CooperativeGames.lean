/-
  Bibliothèque de Théorie des Jeux Coopératifs
  ============================================

  Une bibliothèque Lean 4 formalisant la théorie des jeux coopératifs :
  - Jeux TU (Utilité Transférable)
  - La Valeur de Shapley et ses axiomes
  - Le Cœur et les concepts de stabilité
  - Jeux de vote et indices de pouvoir

  Modules principaux :
  - CooperativeGames.Basic : TUGame, coalitions, Cœur, convexité
  - CooperativeGames.Shapley : axiomes de Shapley, valeur, unicité

  Références :
  - L.S. Shapley, « A Value for N-Person Games » (1953)
  - O. Bondareva, « Some applications of linear programming to cooperative games » (1963)
  - L.S. Shapley, « On balanced sets and cores » (1967)

  ---

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

  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier root
  aggregator est bilingue inline (FR canonique d'abord, EN en miroir).
  Les modules substantiels (`CooperativeGames.Basic`, `CooperativeGames.Shapley`,
  ...) vivent dans des fichiers siblings `_en.lean` séparés.
-/

import CooperativeGames.Basic
import CooperativeGames.Shapley

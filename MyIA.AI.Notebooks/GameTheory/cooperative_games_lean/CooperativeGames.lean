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

  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier root
  aggregator est **FR canonique** uniquement. Le miroir anglais vit dans le
  sibling `CooperativeGames_en.lean` (namespace `CooperativeGames_en`),
  conformément au **modèle sibling pair** ratifié par user le 2026-07-04
  (cf `code-style.md` §Lean i18n, ligne 35 ; Option B rejetée : coût double
  + drift FR/EN + biais qualité). Les modules substantiels
  (`CooperativeGames.Basic`, `CooperativeGames.Shapley`, ...) vivent dans
  des fichiers siblings `_en.lean` séparés, auto-découverts par le
  `globs := #[...]` du lakefile.
-/

import CooperativeGames.Basic
import CooperativeGames.Shapley
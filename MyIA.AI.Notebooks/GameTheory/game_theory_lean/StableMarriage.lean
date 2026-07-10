/-
  GameTheory.StableMarriage — root aggregator (EPIC #4365 phase 4)
  ================================================================

  Ce module agregera les 5 sous-modules absorbes depuis
  `stable_marriage_lean/StableMarriage/` :

  - `StableMarriage.Definitions`      (absorbe c.300)
  - `StableMarriage.GSState`          (c.301)
  - `StableMarriage.Lemmas`           (c.302)
  - `StableMarriage.GaleShapley`      (c.303)
  - `StableMarriage.Lattice`          (c.304)

  La suppression des fichiers source dans `stable_marriage_lean/`
  interviendra en c.305 (PR dediee `debt`/`regression-accepted`,
  cf anti-regression protocol 4 etapes).

  Convention i18n (EPIC #4980 ratifiee user 2026-07-04) : les
  sous-modules `.lean` et leurs siblings `_en.lean` (namespace
  `<Nom>_en`) sont auto-decouverts par le `globs := #[`StableMarriage.*]`
  du lakefile. La CI drift-detection voit les deux langues.
-/

import StableMarriage.Definitions
import StableMarriage.Definitions_en
/-
  GameTheory.StableMarriage — root aggregator (EPIC #4365 phase 4)
  ================================================================

  Ce module regroupe les 5 sous-modules absorbes depuis l'ancien
  `stable_marriage_lean/StableMarriage/` (desormais supprime) :

  - `StableMarriage.Definitions`      (absorbe c.300)
  - `StableMarriage.GSState`          (c.301)
  - `StableMarriage.Lemmas`           (c.302/c.303)
  - `StableMarriage.GaleShapley`      (c.304)
  - `StableMarriage.Lattice`          (c.305)

  La suppression du checkout `stable_marriage_lean/` est effective
  (EPIC #4365 phase 4 ; protocol anti-regression 4 etapes respecte :
  contenu integralement preserve ici, lake build SUCCESS, 0 sorry net
  introduit). Refs prose/CI/inventaire mises a jour vers game_theory_lean.

  Convention i18n (EPIC #4980 ratifiee user 2026-07-04) : les
  sous-modules `.lean` et leurs siblings `_en.lean` (namespace
  `<Nom>_en`) sont auto-decouverts par le `globs := #[`StableMarriage.*]`
  du lakefile. La CI drift-detection voit les deux langues.
-/

import StableMarriage.Definitions
import StableMarriage.Definitions_en
import StableMarriage.GSState
import StableMarriage.GSState_en
import StableMarriage.Lemmas
import StableMarriage.Lemmas_en
import StableMarriage.Lattice
import StableMarriage.Lattice_en
import StableMarriage.GaleShapley
import StableMarriage.GaleShapley_en
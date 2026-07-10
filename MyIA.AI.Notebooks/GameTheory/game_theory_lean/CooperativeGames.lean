/-
  GameTheory.CooperativeGames — root aggregator FR (EPIC #4365 phase 4)
  =====================================================================

  Ce module agrege les sous-modules FR absorbes depuis
  `cooperative_games_lean/CooperativeGames/` (c.306, cette PR) :

  - `CooperativeGames.Basic`        (FR, namespace `TUGame`)
  - `CooperativeGames.ConeKernel`   (FR, namespace `BondarevaCone`,
    importe transitivement par `Basic`)

  Les siblings EN sont **exprès non importes ici** pour eviter une
  collision top-level sur l'abbrev `Coalition` declaree dans Basic.lean
  ET Basic_en.lean (chacun `abbrev Coalition (N : Type*) := Finset N`,
  0 reference interne, jamais documente comme semantiquement distincte —
  cf note interne Basic_en.lean ligne 15 « Acces externe :
  CooperativeGames.TUGame_en.Coalition » qui suggere que la abbrev
  top-level est orpheline des deux cotes). Les modules EN restent
  parfaitement accessibles via `import CooperativeGames.Basic_en` /
  `import CooperativeGames.ConeKernel_en` directement (cf pattern
  valide `decision_theory_lean/Gittins.lean` qui n'importe que les
  modules FR et laisse les `_en` discovers par `globs := #[<Lib>.*]`).

  Pattern miroir : `Probas/decision_theory_lean/{Gittins,Utility,
  Coherence}.lean` (lakefile `globs := #[<Lib>.*]` auto-devoile les
  siblings `_en` sans aggregator EN separe).

  Les modules `CooperativeGames.Shapley` et `CooperativeGames.Shapley_en`
  restent EXCLUS du `globs := #[`CooperativeGames.*]` du lakefile
  (cf `cooperative_games_lean/lakefile.lean` precedent) : bugs residuels
  documentes (`sorry` + `introN failed` + refs `TUGame` a migrer vers
  `TUGame_en`). Absorption separee gated sur resolution de la dette.

  La suppression des fichiers source dans `cooperative_games_lean/`
  interviendra en c.308 (PR dediee `debt`/`regression-accepted`,
  cf anti-regression protocol 4 etapes).

  Convention i18n (EPIC #4980 ratifiee user 2026-07-04) : les
  sous-modules `.lean` et leurs siblings `_en.lean` (namespace
  `<Nom>_en`) sont auto-decouverts par le `globs := #[`CooperativeGames.*]`
  du lakefile. La CI drift-detection voit les deux langues.
-/

import CooperativeGames.Basic
import CooperativeGames.ConeKernel
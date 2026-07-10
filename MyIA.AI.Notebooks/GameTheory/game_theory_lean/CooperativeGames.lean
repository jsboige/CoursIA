/-
  GameTheory.CooperativeGames — root aggregator FR (EPIC #4365 phase 4)
  =====================================================================

  Ce module agrege les sous-modules FR absorbes depuis
  `cooperative_games_lean/CooperativeGames/` :

  - `CooperativeGames.Basic`        (FR, namespace `TUGame`)        — c.306
  - `CooperativeGames.ConeKernel`   (FR, namespace `BondarevaCone`,
    importe transitivement par `Basic`)                             — c.306
  - `CooperativeGames.Shapley`      (FR, namespace `ShapleyValue`)  — c.307b

  Les siblings EN restent **exprès non importes ici** pour eviter une
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

  **Mise a jour c.307b (2026-07-10)** : absorption `CooperativeGames.Shapley`
  ajoutee (FR-only, namespace `ShapleyValue`, 0 sorry tactique, build
  CooperativeGames SUCCESS 8495 jobs firsthand). Le sibling EN
  (`CooperativeGames.Shapley_en`) restait EXCLUS : verifier le commit
  de cette PR revele qu'il reference `TUGame N` (FR namespace) au lieu
  de `TUGame_en` (malgre `open TUGame_en` a L27) sur ~25+ sites (L36, 47,
  50, 57, 61, 68, 72, 79, 92, 110, 186, 200, 207, 326, 419, etc.) —
  bug que l'historique c.234-c.235 documentait comme resolu mais qui
  persistait en realite (lecon L379 NEW c.307b : `grep -nE
  "namespace TUGame\b"` ne verifie que les DECLARATIONS, pas les
  REFERENCES ; `lake build` sibling `_en` = gate obligatoire).

  **Mise a jour c.308 (2026-07-10)** : dette `Shapley_en` payee.
  `CooperativeGames/Shapley_en.lean` byte-copy de `cooperative_games_lean/`
  puis `sed` global `\bTUGame\b -> TUGame_en` (134 sites convertis,
  anti-regression protocole 4 etapes). Le sibling EN est maintenant
  auto-decouvert par `globs := #[`CooperativeGames.*]` (L378 iteration #2
  pattern `decision_theory_lean`), pas d'aggregator EN separe requis.
  Build CooperativeGames SUCCESS 8500 jobs firsthand, Shapley_en.olean
  1840 KB (identique a Shapley FR 1840 KB), 0 sorry tactique.
  Convention i18n validee : meme code tactique, namespaces differencies
  (`TUGame_en` vs `TUGame`), import `CooperativeGames.Basic_en`.

  La suppression des fichiers source dans `cooperative_games_lean/`
  interviendra en c.308+ (PR dediee `debt`/`regression-accepted`,
  cf anti-regression protocol 4 etapes).

  Convention i18n (EPIC #4980 ratifiee user 2026-07-04) : les
  sous-modules `.lean` et leurs siblings `_en.lean` (namespace
  `<Nom>_en`) sont auto-decouverts par le `globs := #[`CooperativeGames.*]`
  du lakefile. La CI drift-detection voit les deux langues.
-/

import CooperativeGames.Basic
import CooperativeGames.ConeKernel
import CooperativeGames.Shapley
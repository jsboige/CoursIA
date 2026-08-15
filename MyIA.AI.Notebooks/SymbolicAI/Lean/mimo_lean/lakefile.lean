import Lake
open Lake DSL

/-!
# Lake mimo_lean — détection MIMO par descente à flips (Lean 4)

Port formel de l'algorithme de détection MIMO par flips de coordonnées
(Papailiopoulos, 2026 — cf issue #10984). Le lake naît directement sur
`v4.32.0` (fin de la migration #10986) :

- **Phase 1** (`Descent.lean`) : squelette de la Proposition 9.1 — descente à
  flips sur un espace d'états abstrait, **sans aucune dépendance** (cœur Lean
  uniquement, build en quelques secondes) : coût strictement décroissant à
  chaque flip accepté, barrière de confinement, plafond de flips `M_N` ⟹ la
  cible est atteinte strictement avant le plafond.
- **Phase 2** (`Objective.lean`, à venir) : fonction objectif du papier avec
  Mathlib — Lemme 11.1 (coût d'un flip) et Lemme 5.1 (erreur LMMSE).
- **Phase 3** (converse §11, à venir) : appui sur le lake externe
  `YuanheZ/lean-stat-learning-theory` (v4.32.0, Apache 2.0) pour la
  concentration gaussienne (Hanson-Wright, LSI, RMT).

Convention i18n #4980 : docstrings FR par défaut, sibling `_en`
(namespace `Mimo_en`, imports `_en`), énoncés et noms de lemmes en anglais.
-/

package «mimo_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «Descent» where
  globs := #[`Descent, `Descent_en]

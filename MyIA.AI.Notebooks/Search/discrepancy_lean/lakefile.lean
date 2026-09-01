import Lake
open Lake DSL

/-!
# Lake `discrepancy_lean` — discrépance combinatoire (issue #12823)

Formalisation de la **discrépance combinatoire** : colorer en `±1` les
éléments d'un système d'ensembles de degré `≤ k` en minimisant la pire somme
colorée. Palier P0 : définitions, conjectures (Beck–Fiala `O(√k)`, Komlós
`O(1)`, formes Bansal–Jiang 2025, arXiv:2508.03961) comme `Prop` nommées,
et l'énoncé cible du théorème classique Beck–Fiala `disc ≤ 2k − 1` — la
« noix » à grignoter par boutes `b1`–`b4` (voir `FORMAL_STATUS.md`).

Conventions du dépôt : docstrings FR-first (#4980), zéro `sorry`, conjecture =
`def ... : Prop` jamais théorème tronqué. Toolchain/manifest alignés sur la
cohorte fleet v4.32.1 (mutualisation #4363).
-/

package «discrepancy_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

/-- Dépendance cross-lake vers le lake frère ML (P2, #12823) : réutilisation
du kernel de concentration `PacLearning.Hoeffding` par import, jamais
dupliqué (mandat FORMAL_STATUS). Les deux lakes partagent mathlib v4.32.1. -/
require learning_theory_lean from ".." / ".." / "ML" / "learning_theory_lean"

@[default_target]
lean_lib «Discrepancy» where
  -- `.submodules` ne build pas le module racine (apprentissage LEAN_INVENTORY) :
  -- on ajoute explicitement l'agrégateur `Discrepancy` au glob.
  -- `Discrepancy_en` : l'agrégateur des siblings EN (#4980), meme raison.
  globs := #[.submodules `Discrepancy, `Discrepancy, `Discrepancy_en]

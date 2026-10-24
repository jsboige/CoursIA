import Lake
open Lake DSL

/-!
# Lake mimo_lean — détection MIMO par descente à flips (Lean 4)

Port formel de l'algorithme de détection MIMO par flips de coordonnées
(Papailiopoulos, 2026 — cf issue #10984). Le lake cible désormais
`v4.33.0` (rollout #14773) — Mathlib résolu à
`db584cd6d46c92f209a44c0f1c829460d327499d` (cf `lake-manifest.json`).

Six libs compilées, deux phases utilitaires + quatre phases du papier §11 :

- **Phase 1 / Descent** (`Descent.lean`) : squelette de la Proposition 9.1 —
  descente à flips sur un espace d'états abstrait, **sans aucune dépendance**
  (cœur Lean uniquement, build en quelques secondes) : coût strictement
  décroissant à chaque flip accepté, barrière de confinement, plafond de
  flips `M_N` ⟹ la cible est atteinte strictement avant le plafond.
- **Phase 2 / Objective** (`Objective.lean`) : fonction objectif au carré avec
  Mathlib — Lemme 11.1 (coût d'un flip, forme fermée) + boucle de contrôle
  `flip_accepted_iff` (pont avec `hstrict` de la Phase 1).
- **Phase 3a / Lmmse** (`Lmmse.lean`) : Lemme 5.1 (erreur LMMSE
  `E‖b − x*‖² = tr B_ρ`) — formule de la trace gaussienne, `B_ρ` PSD,
  transport de loi.
- **Phase 3b / Converse** (`Converse.lean`) : converse §11 — concentration
  Hanson–Wright du bruit (`‖w‖²` chi-square), union bound
  `(1−p)^n ≤ e^{−np}`, appui sur le lake externe
  `YuanheZ/lean-stat-learning-theory` (SLT, base
  `d0f506f0a695018265dccb33bcb05e2f5ca1c876`, Apache 2.0) avec un commit de
  compatibilité Lean 4.33 borné à la preuve du cas de rayon nul.
- **Phase 4 / Bridge** (`Bridge.lean`, grignotage #11148) : pont entre
  `mimoObj` (Phase 2) et converse (Phase 3b) — identité de différence de
  coût `cost_diff`, fragment de converse connecté au ML.
- **Phase 5 / NormTails** (`NormTails.lean`, grignotage #11148) : queues de
  normes `‖w‖`, `‖hᵢ‖` via `gaussian_lipschitz_concentration` du lake SLT
  — concentration 1-Lipschitz de la norme euclidienne.

Convention i18n #4980 : docstrings FR par défaut, sibling `_en`
(namespace `Mimo_en`, imports `_en`), énoncés et noms de lemmes en anglais.
-/

package «mimo_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-
Le fork SLT ajoute à la base upstream d0f506f une unique adaptation de preuve
pour Lean 4.33 ; son lake reste épinglé à Mathlib 4.32. Lake 5 résout les
dépendances directes dans l'ordre inverse de leur déclaration : Mathlib doit
rester en dernier pour que sa fermeture transitive 4.33 (Batteries, Qq, Cli,
etc.) l'emporte sur celle de SLT.
-/
require slt from git
  "https://github.com/jsboige/lean-stat-learning-theory.git" @ "0b1020a4771037b89d0b3809913608d177c09a14"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib «Descent» where
  globs := #[`Descent, `Descent_en]

@[default_target]
lean_lib «Objective» where
  globs := #[`Objective, `Objective_en]

@[default_target]
lean_lib «Lmmse» where
  globs := #[`Lmmse, `Lmmse_en]

@[default_target]
lean_lib «Converse» where
  globs := #[`Converse, `Converse_en]

@[default_target]
lean_lib «Bridge» where
  globs := #[`Bridge, `Bridge_en]

@[default_target]
lean_lib «NormTails» where
  globs := #[`NormTails, `NormTails_en]

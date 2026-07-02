import Sudoku.Basic
import Sudoku.Propagation

/-!
# Sudoku — soundness de la propagation de contraintes (Lean 4)

Formalisation de la **soundness des règles de propagation** d'un Sudoku (naked single,
hidden single), fondement formel des solveurs enseignés dans la série `Sudoku`
(backtracking, OR-Tools, .NET). Voir issue #4055 (roadmap Lean #4038).

## Contenu
- `Sudoku.Basic` : structure de contraintes abstraite — `Scopes` (portées
  toutes-distinctes), `Solution`, `IsSolution`, `AllDistinctOn`, `IsPeer`, `PresentIn`.
  L'abstraction capture tout CSP « à portées toutes-distinctes » (le 9×9 est une
  instance, non un cas spécial).
- `Sudoku.Propagation` : la **clé de voûte** `peer_excludes_value` (une cellule
  affectée exclut sa valeur de ses paires) et les deux théorèmes de soundness
  `naked_single_sound` + `hidden_single_sound`, 0 `sorry`.

## Statut
- Prouvé sans `sorry` : la soundness des règles naked/hidden single (via la clé de
  voûte `peer_excludes_value`). La propagation ne retire **aucune solution valide**.
- Ouvert (jalon suivant) : la **réduction Sudoku ⇔ couverture exacte** (Knuth, 4
  familles de contraintes) et la complétude des règles. Non `sorry`-backed.
- Hors scope : le résultat « 17 indices minimum » (calcul massif, non formalisable).

## Référence croisée
- Série `Sudoku` (C#/.NET + Python) : les solveurs backtracking/OR-Tools/Infer.NET
  dont ce lake fonde formellement l'étape de propagation.
- #2978 (Sudoku comme regex symbolique) : angle Lean = `finiteness-derivatives`
  (terminaison de reconnaisseur), **sans chevauchement** avec la propagation/exact-cover
  formalisés ici (coordination vérifiée).

---

**English — Soundness of Sudoku constraint propagation (Lean 4).**

Formalisation of the **soundness of the propagation rules** of a Sudoku (naked single,
hidden single), the formal foundation of the solvers taught in the `Sudoku` series
(backtracking, OR-Tools, .NET). See issue #4055 (Lean roadmap #4038).

## Contents
- `Sudoku.Basic`: abstract constraint structure — `Scopes` (all-distinct scopes),
  `Solution`, `IsSolution`, `AllDistinctOn`, `IsPeer`, `PresentIn`. The abstraction
  captures any "all-distinct-scopes" CSP (the 9×9 grid is one instance, not a special
  case).
- `Sudoku.Propagation`: the **keystone** `peer_excludes_value` (an assigned cell excludes
  its value from all its peers) and the two soundness theorems `naked_single_sound` +
  `hidden_single_sound`, 0 `sorry`.

## Status
- Proved without `sorry`: soundness of the naked/hidden single rules (via the keystone
  `peer_excludes_value`). Propagation removes **no valid solution**.
- Open (next milestone): the **Sudoku ⇔ exact-cover reduction** (Knuth, 4 constraint
  families) and completeness of the rules. Not `sorry`-backed.
- Out of scope: the "17-clue minimum" result (massive computation, not formalisable).

## Cross-reference
- `Sudoku` series (C#/.NET + Python): the backtracking/OR-Tools/Infer.NET solvers whose
  propagation step this lake formally grounds.
- #2978 (Sudoku as a symbolic regex): the Lean angle is `finiteness-derivatives`
  (recogniser termination), **without overlap** with the propagation/exact-cover
  formalised here (coordination verified).
-/

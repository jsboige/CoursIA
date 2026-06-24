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
-/

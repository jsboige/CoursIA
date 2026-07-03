import Sudoku.Basic
import Sudoku.Propagation
import Sudoku.ExactCover

/-!
# Sudoku — soundness de la propagation + réduction exact-cover (Lean 4)

Formalisation de la **soundness des règles de propagation** d'un Sudoku (naked single,
hidden single) et de la **réduction Sudoku ⇔ couverture exacte** (Knuth), fondement
formel des solveurs enseignés dans la série `Sudoku` (backtracking, OR-Tools, .NET).
Voir issue #4055 (roadmap Lean #4038).

## Contenu
- `Sudoku.Basic` : structure de contraintes abstraite — `Scopes` (portées
  toutes-distinctes), `Solution`, `IsSolution`, `AllDistinctOn`, `IsPeer`, `PresentIn`.
  L'abstraction capture tout CSP « à portées toutes-distinctes » (le 9×9 est une
  instance, non un cas spécial).
- `Sudoku.Propagation` : la **clé de voûte** `peer_excludes_value` (une cellule
  affectée exclut sa valeur de ses paires) et les deux théorèmes de soundness
  `naked_single_sound` + `hidden_single_sound`, 0 `sorry`.
- `Sudoku.ExactCover` : la réduction Sudoku ⇔ couverture exacte (Knuth, encodage
  4 familles → 2 dans le cadre abstrait). Le théorème capstone `sudoku_iff_exact_cover`
  prouve l'**équivalence complète** : `solution_imp_exact_cover` (sens direct, via
  `toSelection` et le lemme de pleine maison `full_house_present`) +
  `exact_cover_imp_solution` (sens retour, via la construction inverse `fromSelection`),
  0 `sorry`.

## Statut
- Prouvé sans `sorry` : (1) la soundness des règles naked/hidden single (clé de
  voûte `peer_excludes_value`, la propagation ne retire aucune solution valide) ;
  (2) l'**équivalence complète** Sudoku ⇔ couverture exacte — `(∃ σ, IsSolution
  scopes σ) ↔ (∃ sel, IsExactCover sel scopes)` sous l'hypothèse « pleine maison »
  (satisfaite par le 9×9 où chaque portée a 9 cellules pour 9 valeurs), en deux
  temps : sens direct `solution_imp_exact_cover` + sens retour
  `exact_cover_imp_solution`.
- Axiomes : trio standard du noyau Lean 4 (`propext`, `Classical.choice`,
  `Quot.sound`) — `Classical.choice` intervient pour la construction non
  constructive `fromSelection` (extraire un témoin par cellule depuis l'`∃!` de
  couverture). Aucun axiome ad hoc.
- Hors scope : le résultat « 17 indices minimum » (calcul massif, non formalisable).

## Référence croisée
- Série `Sudoku` (C#/.NET + Python) : les solveurs backtracking/OR-Tools/Infer.NET
  dont ce lake fonde formellement l'étape de propagation.
- #2978 (Sudoku comme regex symbolique) : angle Lean = `finiteness-derivatives`
  (terminaison de reconnaisseur), **sans chevauchement** avec la propagation/exact-cover
  formalisés ici (coordination vérifiée).
-/

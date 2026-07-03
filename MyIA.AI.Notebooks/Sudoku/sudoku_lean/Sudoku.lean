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
  4 familles → 2 dans le cadre abstrait). `solution_imp_exact_cover` prouve le
  **sens direct** (une solution est une couverture exacte, via `toSelection` et le
  lemme de pleine maison `full_house_present`), 0 `sorry`.

## Statut
- Prouvé sans `sorry` : (1) la soundness des règles naked/hidden single (clé de
  voûte `peer_excludes_value`, la propagation ne retire aucune solution valide) ;
  (2) le **sens direct** de la réduction exact-cover — `IsSolution scopes σ →
  IsExactCover (toSelection σ) scopes` sous l'hypothèse « pleine maison »
  (satisfaite par le 9×9 où chaque portée a 9 cellules pour 9 valeurs).
- Ouvert (jalon suivant) : le **sens retour** (couverture exacte ⇒ solution) et
  l'équivalence complète `sudoku_iff_exact_cover`. Délibérément **non `sorry`-backed**,
  pour garder la bibliothèque entièrement `sorry`-free.
- Hors scope : le résultat « 17 indices minimum » (calcul massif, non formalisable).

## Référence croisée
- Série `Sudoku` (C#/.NET + Python) : les solveurs backtracking/OR-Tools/Infer.NET
  dont ce lake fonde formellement l'étape de propagation.
- #2978 (Sudoku comme regex symbolique) : angle Lean = `finiteness-derivatives`
  (terminaison de reconnaisseur), **sans chevauchement** avec la propagation/exact-cover
  formalisés ici (coordination vérifiée).
-/

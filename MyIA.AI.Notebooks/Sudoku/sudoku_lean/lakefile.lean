import Lake
open Lake DSL

/-!
# Mini-projet Lean pédagogique : soundness de la propagation de contraintes Sudoku

Projet Lean 4 (avec Mathlib) prouvant la **soundness des règles de propagation** d'un
Sudoku (naked single, hidden single) : ces règles, utilisées par tous les solveurs
enseignés dans la série `Sudoku` (backtracking, OR-Tools, .NET), **ne retirent aucune
solution valide** — elles ne font qu'éliminer des affectations impossibles. Voir
l'issue #4055 (roadmap Lean #4038). Coordination #2978 vérifiée : l'angle Lean de
#2978 est la terminaison de reconnaisseur regex (`finiteness-derivatives`), sans
chevauchement avec la propagation/exact-cover formalisés ici.

Premier théorème Lean de la série **Sudoku**. La formalisation est **abstraite sur la
structure de contraintes** (un Sudoku = un ensemble de « portées » `scopes`, chacune
devant porter des valeurs toutes distinctes) : les théorèmes de soundness sont valables
pour toute structure de ce type (lignes, colonnes, blocs du 9×9, mais aussi tout CSP
à portées toutes-distinctes). La 9×9 concrète est une instance, non un cas spécial.

**Clé de voûte** : `peer_excludes_value` — une cellule affectée exclut sa valeur de
toutes ses cellules « paires » (même portée) dans toute solution. C'est le fait
fondamental dont dérivent les règles de propagation :

- `naked_single_sound` : si toutes les valeurs sauf `v` sont déjà présentes parmi les
  paires d'une cellule, toute solution y place `v`.
- `hidden_single_sound` : si une valeur ne peut aller que dans une seule cellule d'une
  portée, toute solution l'y place.

L'équivalence Sudoku ⇔ couverture exacte (Knuth, 4 familles de contraintes) est un
jalon naturel laissé ouvert (non `sorry`-backed) — la soundness de la propagation est
livrée intégralement.

Mathlib fournit `Finset`, l'injectivité sur un ensemble (`Set.InjOn`), et l'arithmétique
des images finies nécessaires.

Notebook compagnon (série `Sudoku`) : présentation pédagogique des solveurs par
propagation. Le câblage du notebook revient au propriétaire de la série Sudoku
(convention des lakes frères : le lake est le livrable formel, le `lake build` est la
preuve d'exécution).
-/

package «sudoku_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

@[default_target]
lean_lib «Sudoku» where
  globs := #[.submodules `Sudoku]

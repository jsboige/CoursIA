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

---

**English — Pedagogical Lean mini-project: soundness of Sudoku constraint propagation.**

A Lean 4 (with Mathlib) project proving the **soundness of the propagation rules** of a
Sudoku (naked single, hidden single): these rules, used by every solver taught in the
`Sudoku` series (backtracking, OR-Tools, .NET), **remove no valid solution** — they only
eliminate impossible assignments. See issue #4055 (Lean roadmap #4038). Coordination
#2978 verified: the Lean angle of #2978 is regex-recogniser termination
(`finiteness-derivatives`), without overlap with the propagation/exact-cover formalised
here.

First Lean theorem of the **Sudoku** series. The formalisation is **abstract over the
constraint structure** (a Sudoku = a set of "scopes" `scopes`, each of which must carry
all-distinct values): the soundness theorems hold for any structure of this kind (rows,
columns, 3×3 blocks of the 9×9 grid, but also any all-distinct-scopes CSP). The concrete
9×9 grid is one instance, not a special case.

**Keystone**: `peer_excludes_value` — an assigned cell excludes its value from all its
"peer" cells (same scope) in any solution. This is the fundamental fact from which the
propagation rules derive:

- `naked_single_sound`: if every value but `v` is already present among a cell's peers,
  every solution places `v` there.
- `hidden_single_sound`: if a value can go in only one cell of a scope, every solution
  places it there.

The Sudoku ⇔ exact-cover equivalence (Knuth, 4 constraint families) is a natural milestone
left open (not `sorry`-backed) — propagation soundness is delivered in full.

Mathlib provides `Finset`, injectivity on a set (`Set.InjOn`), and the finite-image
arithmetic needed.

Companion notebook (`Sudoku` series): pedagogical presentation of propagation-based
solvers. Wiring the notebook is the responsibility of the Sudoku series owner (sibling-lake
convention: the lake is the formal deliverable, `lake build` is the execution proof).
-/

package «sudoku_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

@[default_target]
lean_lib «Sudoku» where
  globs := #[.submodules `Sudoku]

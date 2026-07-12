/-!
# Astar — racine du sous-lac `search_lean` (A* optimalité)

Agrégateur canonique français du sous-lac `search_lean` (namespace `Astar`).
Regroupe les quatre briques de la formalisation en Lean 4 / Mathlib 4 de
l'**optimalité de A*** sous heuristique admissible (Hart, Nilsson & Raphael,
1968).

## Contenu du sous-lac

- `Astar.Graph` — modèle abstrait : graphe orienté pondéré à arêtes
  non-négatives (`NNReal`), chemins comme listes de sommets, coût d'un chemin
  comme somme des poids des arcs consécutifs.
- `Astar.Heuristic` — définitions centrales : heuristique `h : V → NNReal`,
  « vrai coût optimal restant » `hStar`, conditions d'**admissibilité**
  (`h ≤ hStar`) et de **consistance** (relaxation de Bellman,
  `h n ≤ edge n n' + h n'`).
- `Astar.Optimality` — théorème phare (registre **#3801** prong B « problème
  non-trivial », cf. aussi **#4048** et la roadmap **#4038**) : sous
  heuristique admissible, la borne en `f = g + h` reste sous le coût optimal
  en tout point d'un chemin optimal. Formalisé par un **lemme abstrait
  d'optimalité**, sans modéliser la file de priorité complète.
- `Astar.Consistency` — pont localité/globalité : la **consistance**
  (condition locale par arc) **implique l'admissibilité** (condition globale
  par chemin), par **téléscopage** le long des arcs.

## Convention i18n #4980 (sibling pair)

Le sous-lac applique la convention ratifiée 2026-07-04 par ai-01 :
**FR canonique + EN sibling `_en.lean` par module**, namespace distinct
(`Astar` ↔ `Astar_en`) pour éviter toute collision de noms. Le présent
fichier (`Astar.lean`) est la racine canonique française ; son jumeau
monolingue anglais `Astar_en.lean` est strictement additif (mêmes imports,
même ordre, imports byte-identiques au bit près).

Une companion markdown `Astar.en.md` complète la documentation par une
traduction anglaise narrative hors-compilation (option B #4980, pilote
`sudoku_lean` PR #4998).

## Notebooks compagnons

Série `Search/Part1-Foundations/` :

- `Search-2-Uninformed.ipynb` — recherche non informée (DFS, BFS, UCS)
  avec **contre-exemple BFS-vs-UCS** motivant l'apport de A*.
- `Search-3-Informed.ipynb` — heuristiques admissibles/consistantes et
  garantie d'optimalité, en regard direct avec les preuves `Astar.Optimality`
  et `Astar.Consistency`.
-/

import Astar.Graph
import Astar.Heuristic
import Astar.Optimality
import Astar.Consistency

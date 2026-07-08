# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

## csp1-backtracking-tree.png

- **Source** : notebook `CSP-1-Fundamentals.ipynb` (cellule 9, output 0)
- **Alt-text (FR)** : Arbre de backtracking pour le probleme des 4 reines : exploration avec heuristique MRV (Minimum Remaining Values), montrant l'elagage des branches invalides des la premiere variable contrainte.
- **Poids** : 29.0 KB (PIL optimise)

## csp2-ac3-propagation.png

- **Source** : notebook `CSP-2-Consistency.ipynb` (cellule 20, output 0)
- **Alt-text (FR)** : Propagation de contraintes AC-3 sur un reseau de contraintes binaires : reduction des domaines par arc-coherence, l'espace de recherche se ressedement avant tout essai de valeur.
- **Poids** : 92.0 KB (PIL optimise)

## csp3-global-constraints.png

- **Source** : notebook `CSP-3-Advanced.ipynb` (cellule 10, output 0)
- **Alt-text (FR)** : Contrainte globale AllDifferent d'OR-Tools CP-SAT sur un Sudoku-like : le propagateur specialise elague en quelques millisecondes ce qu'un backtracking naif mettrait des heures a parcourir.
- **Poids** : 29.9 KB (PIL optimise)

## csp4-jobshop-gantt.png

- **Source** : notebook `CSP-4-Scheduling.ipynb` (cellule 7, output 0)
- **Alt-text (FR)** : Diagramme de Gantt d'un ordonnancement Job-Shop (JSSP) resolu par CP-SAT avec IntervalVar et NoOverlap : chevauchement optimal des operations sur les machines.
- **Poids** : 21.6 KB (PIL optimise)

## csp6-lazy-clause-generation.png

- **Source** : notebook `CSP-6-Hybridization.ipynb` (cellule 20, output 0)
- **Alt-text (FR)** : Lazy Clause Generation (LCG) : le solveur CP apprend des clauses SAT en cours de route, visualisation des clauses apprises qui coupent l'espace de recherche lors des retours arriere.
- **Poids** : 36.1 KB (PIL optimise)

## csp8-allen-algebra.png

- **Source** : notebook `CSP-8-Temporal.ipynb` (cellule 6, output 0)
- **Alt-text (FR)** : Algèbre d'intervalles d'Allen : les 13 relations temporelles de base entre deux intervalles (avant, apres, pendant, etc.) et leur composition pour raisonner sur des contraintes de temps qualitatif.
- **Poids** : 36.9 KB (PIL optimise)

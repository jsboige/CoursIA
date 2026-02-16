# Search - Fondations algorithmiques

Sous-serie de **8 notebooks** couvrant les algorithmes fondamentaux de recherche et de programmation par contraintes.

## Progression

```
Search-1  Espaces d'etats
    |
Search-2  Recherche non informee (BFS, DFS, UCS, IDDFS)
    |
    +---> Search-3  Recherche informee (A*, Greedy, IDA*)
    |
    +---> Search-4  Recherche locale (Hill Climbing, SA, Tabu)
              |
              +---> Search-5  Algorithmes genetiques (DEAP, PyGAD)
    |
Search-6  CSP - Fondamentaux (backtracking, MRV, LCV)
    |
Search-7  CSP - Consistance (AC-3, Forward checking, MAC)
    |
Search-8  CSP - Avance (AllDifferent, cumulative, LNS)
```

## Notebooks

| # | Notebook | Duree | Contenu | Prerequis |
|---|----------|-------|---------|-----------|
| 1 | [Search-1-StateSpace](Search-1-StateSpace.ipynb) | ~40 min | Formalisation (S, A, T, G), taquin, aspirateur, route | Python basique |
| 2 | [Search-2-Uninformed](Search-2-Uninformed.ipynb) | ~50 min | BFS, DFS, UCS, IDDFS, complexites | Search-1 |
| 3 | [Search-3-Informed](Search-3-Informed.ipynb) | ~50 min | A*, Greedy, IDA*, heuristiques | Search-2 |
| 4 | [Search-4-LocalSearch](Search-4-LocalSearch.ipynb) | ~45 min | Hill Climbing, SA, Tabu Search | Search-2 |
| 5 | [Search-5-GeneticAlgorithms](Search-5-GeneticAlgorithms.ipynb) | ~50 min | Selection, crossover, mutation, DEAP | Search-4 |
| 6 | [Search-6-CSP-Fundamentals](Search-6-CSP-Fundamentals.ipynb) | ~50 min | Variables, domaines, contraintes, backtracking | Search-1 |
| 7 | [Search-7-CSP-Consistency](Search-7-CSP-Consistency.ipynb) | ~45 min | AC-3, Forward checking, MAC | Search-6 |
| 8 | [Search-8-CSP-Advanced](Search-8-CSP-Advanced.ipynb) | ~50 min | AllDifferent, cumulative, circuit, LNS | Search-7 |

**Duree totale** : ~6h20

## Vers les Applications

Apres avoir complete cette sous-serie, explorez les [Applications](../Applications/README.md) pour voir ces algorithmes en action sur des problemes du monde reel.

| Fondation | Applications associees |
|-----------|----------------------|
| Search-4 (Local Search) | App-4 (Job-Shop), App-10 (Portfolio) |
| Search-5 (GA) | App-9 (Edge Detection), App-10 (Portfolio) |
| Search-6 (CSP) | App-1 (N-Queens), App-2 (Graph Coloring) |
| Search-7 (Consistency) | App-6 (Minesweeper), App-7 (Wordle) |
| Search-8 (CSP Advanced) | App-3 (Nurse), App-4 (Job-Shop), App-8 (MiniZinc) |

Voir aussi la serie [Sudoku](../../Sudoku/README.md) pour une application complete des CSP avec 6+ solveurs differents.

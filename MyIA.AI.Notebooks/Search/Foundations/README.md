# Search - Fondations algorithmiques

Sous-serie de **12 notebooks** couvrant les algorithmes fondamentaux de recherche, de programmation par contraintes, et de techniques d'optimisation avancees.

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
              +---> Search-9  Metaheuristiques (MEALPy: PSO, ABC, SA)
    |
Search-6  CSP - Fondamentaux (backtracking, MRV, LCV)
    |
Search-7  CSP - Consistance (AC-3, Forward checking, MAC)
    |
Search-8  CSP - Avance (AllDifferent, cumulative, LNS)
    |
    +---> Search-10  Dancing Links (Algorithm X, DLX)
    |
Search-11  Programmation Lineaire (PuLP, simplex, transport)
    |
Search-12  Automates Symboliques (Z3, automata-lib)
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
| 9 | [Search-9-Metaheuristics](Search-9-Metaheuristics.ipynb) | ~1h30 | PSO, ABC, SA, BRO avec MEALPy, benchmark comparatif | Search-4, Search-5 |
| 10 | [Search-10-DancingLinks](Search-10-DancingLinks.ipynb) | ~1h30 | Algorithme X, DLX, Sudoku, N-Queens, Pentominoes | Search-2 |
| 11 | [Search-11-LinearProgramming](Search-11-LinearProgramming.ipynb) | ~2h | PuLP, simplex, transport, diet, sensibilite, PLNE | Algebre lineaire |
| 12 | [Search-12-SymbolicAutomata](Search-12-SymbolicAutomata.ipynb) | ~2h | DFA/NFA (automata-lib), predicats Z3, automates symboliques | Search-1, SymbolicAI/Z3 |

**Duree totale** : ~13h30

## Vers les Applications

Apres avoir complete cette sous-serie, explorez les [Applications](../Applications/README.md) pour voir ces algorithmes en action sur des problemes du monde reel.

| Fondation | Applications associees |
|-----------|----------------------|
| Search-4 (Local Search) | App-4 (Job-Shop), App-10 (Portfolio) |
| Search-5 (GA) | App-9 (Edge Detection), App-10 (Portfolio) |
| Search-6 (CSP) | App-1 (N-Queens), App-2 (Graph Coloring) |
| Search-7 (Consistency) | App-6 (Minesweeper), App-7 (Wordle) |
| Search-8 (CSP Advanced) | App-3 (Nurse), App-4 (Job-Shop), App-8 (MiniZinc) |
| Search-9 (Metaheuristics) | Optimisation continue, benchmark |
| Search-10 (Dancing Links) | App-11 (Picross), Sudoku-5 (DLX) |
| Search-11 (Linear Programming) | App-10 (Portfolio optimisation) |
| Search-12 (Symbolic Automata) | Sudoku-12 (Automata symboliques) |

## Series connexes

- **[Sudoku](../../Sudoku/README.md)** : Application complete des CSP et automates symboliques avec 17 solveurs differents
- **[SymbolicAI](../../SymbolicAI/README.md)** : Z3, RDF, Lean, et automates symboliques
- **[GenAI](../../GenAI/README.md)** : Optimisation d'hyperparametres avec metaheuristiques

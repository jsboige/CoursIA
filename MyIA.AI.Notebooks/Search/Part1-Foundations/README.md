# Partie 1 : Search Fondamental

Algorithmes de recherche classiques et metaheuristiques.

## Notebooks

| # | Notebook | Duree | Contenu | Prerequis |
|---|----------|-------|---------|-----------|
| 1 | [Search-1-StateSpace](Search-1-StateSpace.ipynb) | ~40 min | Espaces d'etats, formalisation (S, A, T, G), taquin, aspirateur, route | Python basique |
| 2 | [Search-2-Uninformed](Search-2-Uninformed.ipynb) | ~50 min | BFS, DFS, UCS, IDDFS, comparaison systematique | Search-1 |
| 3 | [Search-3-Informed](Search-3-Informed.ipynb) | ~50 min | A*, Greedy, IDA*, heuristiques admissibles et consistantes | Search-2 |
| 4 | [Search-4-LocalSearch](Search-4-LocalSearch.ipynb) | ~45 min | Hill Climbing, Simulated Annealing, Tabu Search, paysages de fitness | Search-2 |
| 5 | [Search-5-GeneticAlgorithms](Search-5-GeneticAlgorithms.ipynb) | ~50 min | Selection, crossover, mutation, DEAP/PyGAD, theorie unifiee | Search-4 |
| 6 | [Search-6-AdversarialSearch](Search-6-AdversarialSearch.ipynb) | ~1h | Minimax, Alpha-Beta pruning, Null-window search, Transposition tables | Search-2, Search-3 |
| 7 | [Search-7-MCTS-And-Beyond](Search-7-MCTS-And-Beyond.ipynb) | ~1h30 | MCTS, UCB1, OpenSpiel, AlphaGo-style (DQN+MCTS) | Search-6 |
| 8 | [Search-8-DancingLinks](Search-8-DancingLinks.ipynb) | ~1h30 | Algorithme X, DLX, Sudoku, N-Queens, Pentominoes | Search-2 |
| 9 | [Search-9-LinearProgramming](Search-9-LinearProgramming.ipynb) | ~2h | PuLP, simplex, transport, diet, sensibilite, PLNE | Algebre lineaire |
| 10 | [Search-10-SymbolicAutomata](Search-10-SymbolicAutomata.ipynb) | ~2h | DFA/NFA (automata-lib), predicats Z3, automates symboliques | Search-1, SymbolicAI/Z3 |
| 11 | [Search-11-Metaheuristics](Search-11-Metaheuristics.ipynb) | ~1h30 | PSO, ABC, SA, BRO avec MEALPy, benchmark comparatif | Search-4, Search-5 |

## Progression recommandee

```text
Search-1 (StateSpace)
    │
    └──> Search-2 (Uninformed)
              │
              ├──> Search-3 (Informed)
              │         │
              │         └──> Search-6 (AdversarialSearch)
              │                   │
              │                   └──> Search-7 (MCTS-And-Beyond)
              │
              ├──> Search-4 (LocalSearch)
              │        │
              │        └──> Search-5 (GeneticAlgorithms)
              │                  │
              │                  └──> Search-11 (Metaheuristics)
              │
              └──> Search-8 (DancingLinks)

Search-9 (LinearProgramming) - independant
Search-10 (SymbolicAutomata) - liens avec SymbolicAI
```

## Retour

[<- Retour a la serie Search](../README.md)

# Partie 1 : Search Fondamental

[↑ Serie Search](../README.md) | [Partie 2 : CSP →](../Part2-CSP/README.md)

Comment passer d'une enumeration exhaustive a une exploration intelligemment guidee d'un espace d'etats ? Cette premiere partie couvre les trois grands paradigmes de la recherche en IA : systematique (BFS, A*), locale (Hill Climbing, recuit simule) et evolutive (algorithmes genetiques, PSO). Le fil rouge est la reduction progressive de l'espace de recherche, depuis la formalisation du probleme jusqu'aux metaheuristiques comparees sur des benchmarks.

Vous commencerez par poser le cadre formel (S, A, T, G) dans Search-1, puis decouvrirez les algorithmes non informes et informes, la recherche locale et genetique, la recherche adversariale (Minimax, MCTS) et les extensions que sont la programmation lineaire, les automates symboliques et les metaheuristiques.

## Objectifs d'apprentissage

A l'issue de cette partie, vous serez capable de :

1. **Formaliser** un probleme sous forme d'espace d'etats (S, A, T, G) et l'implementer en Python
2. **Choisir** l'algorithme de recherche adapte au probleme : systematique (BFS, A*), locale (SA, Tabu), ou evolutive (GA, PSO)
3. **Concevoir et evaluer** des heuristiques admissibles et consistantes pour guider la recherche
4. **Appliquer** la recherche adversariale (Minimax, Alpha-Beta, MCTS) aux jeux a deux joueurs
5. **Comparer** les metaheuristiques sur des benchmarks reels et justifier le choix d'un algorithme

## Notebooks

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 1 | [Search-1-StateSpace](Search-1-StateSpace.ipynb) | Python 3 | Espaces d'etats, formalisation (S, A, T, G), taquin, aspirateur, recherche d'itineraire | ~40 min |
| 2 | [Search-2-Uninformed](Search-2-Uninformed.ipynb) | Python 3 | BFS, DFS, UCS, IDDFS : comparaison des algorithmes non informes | ~50 min |
| 3 | [Search-3-Informed](Search-3-Informed.ipynb) | Python 3 | A*, Greedy, IDA*, heuristiques admissibles et consistantes | ~50 min |
| 4 | [Search-4-LocalSearch](Search-4-LocalSearch.ipynb) | Python 3 | Hill Climbing, Simulated Annealing, Tabu Search, paysages de fitness | ~45 min |
| 5 | [Search-5-GeneticAlgorithms](Search-5-GeneticAlgorithms.ipynb) | Python 3 | Selection, crossover, mutation, DEAP/PyGAD, theorie unifiee | ~50 min |
| 6 | [Search-6-AdversarialSearch](Search-6-AdversarialSearch.ipynb) | Python 3 | Minimax, Alpha-Beta pruning, Null-window search, tables de transposition | ~1h |
| 7 | [Search-7-MCTS-And-Beyond](Search-7-MCTS-And-Beyond.ipynb) | Python 3 | Monte Carlo Tree Search, UCB1, OpenSpiel, architecture AlphaGo (DQN+MCTS) | ~1h30 |
| 8 | [Search-8-DancingLinks](Search-8-DancingLinks.ipynb) | Python 3 | Algorithme X de Knuth, Dancing Links (DLX), couverture exacte (Sudoku, N-Queens, Pentominoes) | ~1h30 |
| 9 | [Search-9-LinearProgramming](Search-9-LinearProgramming.ipynb) | Python 3 | Programmation lineaire avec PuLP, simplex, probleme du transport, diet problem, PLNE | ~2h |
| 10 | [Search-10-SymbolicAutomata](Search-10-SymbolicAutomata.ipynb) | Python 3 | Automates finis (DFA/NFA) avec automata-lib, predicats Z3, automates symboliques | ~2h |
| 11 | [Search-11-Metaheuristics](Search-11-Metaheuristics.ipynb) | Python 3 | PSO, ABC, SA, BRO avec MEALPy, benchmark comparatif de metaheuristiques | ~1h30 |

## Progression

Les notebooks 1 a 3 forment le socle commun (formalisation, recherche systematique). A partir de Search-2, le parcours se divise en quatre branches :

- **Recherche locale et evolutive** : Search-4 (LocalSearch) puis Search-5 (GeneticAlgorithms) puis Search-11 (Metaheuristics)
- **Recherche dans les jeux** : Search-3 puis Search-6 (AdversarialSearch) puis Search-7 (MCTS)
- **Couverture exacte** : Search-2 puis Search-8 (DancingLinks)
- **Independants** : Search-9 (LinearProgramming, algebre lineaire requise) et Search-10 (SymbolicAutomata, liens avec SymbolicAI/Z3)

Les fondamentaux de cette partie (formalisation, backtracking, heuristiques) sont le prerequis de la [Partie 2 (CSP)](../Part2-CSP/README.md).

## Prerequis & environnement

| Besoin | Detail |
|--------|--------|
| Python | 3.10+, environnement virtuel recommande |
| `ortools` | Search-9 (Linear Programming) |
| `deap` | Search-5 (Genetic Algorithms) |
| `mealpy` | Search-11 (Metaheuristiques) |
| `z3-solver` | Search-10 (Symbolic Automata) |
| OpenSpiel | Search-7 (MCTS) : requiert WSL ou Linux |

Pour le setup complet, voir le [README de la serie Search](../README.md).

## FAQ

| Probleme | Solution |
|----------|----------|
| A* trop lent sur les grands graphes | Verifier que l'heuristique est admissible ET consistante ; essayer IDA* (Search-3), qui consomme moins de memoire |
| GA stagne sans amelioration | Augmenter le taux de mutation ou la taille de la population ; comparer avec les metaheuristiques de Search-11 |

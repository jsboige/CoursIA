# Partie 1 : Search Fondamental

Cette partie couvre les **algorithmes de recherche classiques**, depuis l'exploration systematique d'espaces d'etats (BFS, DFS, A*) jusqu'aux metaheuristiques inspirees de la nature (algorithmes genetiques, PSO). Le fil rouge est la reduction progressive de l'espace de recherche : comment passer d'une enumeration aveugle a une exploration intelligemment guidee.

Vous commencerez par formaliser des problemes sous forme d'espaces d'etats (Search-1), puis decouvrirez les trois grands paradigmes : recherche systematique (BFS/A*), optimisation locale (Hill Climbing, recuit simule), et recherche dans les jeux (Minimax, MCTS). Les notebooks avances couvrent des extensions industrielles (programmation lineaire, automates symboliques, metaheuristiques comparees).

**11 notebooks** | **~12h30** | Python 3.10+ (`ortools`, `deap`, `mealpy`, `z3-solver`)

## Pourquoi cette sous-serie

La recherche est le pilier de l'IA classique : tout probleme peut se ramener a l'exploration d'un espace d'etats. Cette partie couvre les **trois grands paradigmes** (systematique, locale, evolutive) avec une progression qui va de la theorie (formalisation) a la pratique (benchmarks reels). Le fil rouge est la reduction progressive de l'espace de recherche : comment passer d'une enumeration aveugle a une exploration intelligemment guidee.

Ces fondamentaux sont le prerequis de [Partie 2 (CSP)](../Part2-CSP/README.md) et des [Applications](../Applications/README.md) — maitriser les algorithmes de cette partie est essentiel avant de passer aux contraintes et aux projets.

## Objectifs d'apprentissage

A l'issue de cette partie, vous serez capable de :

1. **Formaliser** un probleme sous forme d'espace d'etats (S, A, T, G) et l'implementer en Python
2. **Choisir** l'algorithme de recherche adapte au probleme : systematique (BFS, A*), locale (SA, Tabu), ou evolutive (GA, PSO)
3. **Concevoir et evaluer** des heuristiques admissibles et consistantes pour guider la recherche
4. **Appliquer** la recherche adversariale (Minimax, Alpha-Beta, MCTS) aux jeux a deux joueurs
5. **Comparer** les metaheuristiques sur des benchmarks reels et justifier le choix d'un algorithme

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

### Ce que chaque notebook apporte

**Search-1 (StateSpace)** pose les fondations : qu'est-ce qu'un probleme de recherche ? Vous apprendrez a definir un espace d'etats (etats initiaux, actions, transitions, buts) et a implementer le taquin, l'aspirateur et la recherche d'itineraire comme des instances de ce cadre general. Ce notebook est le prerequis de toute la serie.

**Search-2 (Uninformed)** et **Search-3 (Informed)** couvrent les deux faces de la recherche systematique. Le notebook 2 compare BFS, DFS, UCS et IDDFS sans aucune connaissance du domaine. Le notebook 3 introduit les heuristiques et montre comment A* garantie l'optimalite quand l'heuristique est admissible et consistante -- un resultat central.

**Search-4 (LocalSearch)** pivote vers l'optimisation locale : Hill Climbing (avec ses plateaux et creux), Simulated Annealing (recuit simule, parametres de temperature) et Tabu Search. Vous visualiserez les paysages de fitness pour comprendre pourquoi la recherche locale reste bloquee.

**Search-5 (GeneticAlgorithms)** passe a l'evolution : selection, crossover, mutation, remplacement. Implementations avec DEAP et PyGAD, avec une perspective unifiee reliant GA a l'optimisation locale.

**Search-6 (AdversarialSearch)** et **Search-7 (MCTS)** couvrent la recherche dans les jeux a deux joueurs. Le notebook 6 traite Minimax, Alpha-Beta pruning et les tables de transposition. Le notebook 7 va plus loin avec Monte Carlo Tree Search (UCB1), l'integration OpenSpiel et l'architecture AlphaGo (DQN + MCTS).

**Search-8 (DancingLinks)** explore l'algorithme X de Knuth et la structure de donnees DLX (Dancing Links) pour la couverture exacte -- au coeur de la resolution de Sudoku, N-Queens et Pentominoes.

**Search-9 (LinearProgramming)** ouvre la boite a outils de l'optimisation lineaire (PuLP, simplex) : probleme du transport, diet problem, analyse de sensibilite, programmation lineaire en nombres entiers (PLNE). Notebook independant, utile pour les applications CSP et hybrides.

**Search-10 (SymbolicAutomata)** croise la recherche avec l'IA symbolique : automates finis (DFA/NFA) avec la librairie `automata-lib`, puis automates symboliques avec predicats Z3. Connections naturelles vers la serie SymbolicAI.

**Search-11 (Metaheuristiques)** compare PSO (Particle Swarm Optimization), ABC (Artificial Bee Colony), SA (recuit simule) et BRO avec MEALPy sur un benchmark. Conclusion pratique : quel algorithme choisir selon le probleme ?

## FAQ / Troubleshooting

| Probleme | Solution |
|----------|----------|
| `ModuleNotFoundError: ortools` | `pip install ortools` — necessaire pour Search-9 (Linear Programming) et les applications CSP |
| `ModuleNotFoundError: deap` | `pip install deap` — necessaire pour Search-5 (Genetic Algorithms) |
| `ModuleNotFoundError: mealpy` | `pip install mealpy` — necessaire pour Search-11 (Metaheuristiques) |
| `ModuleNotFoundError: z3-solver` | `pip install z3-solver` — necessaire pour Search-10 (Symbolic Automata) |
| Search-7 (MCTS) : OpenSpiel ne s'installe pas sur Windows | OpenSpiel requiert WSL ou Linux. Les notebooks 1-6 et 8-11 fonctionnent sous Windows natif |
| A* trop lent sur les grands graphes | Verifier que l'heuristique est admissible ET consistante. Essayer IDA* (notebook 3) qui consomme moins de memoire |
| GA stagne sans amelioration | Augmenter le taux de mutation ou la taille de la population. Explorer le notebook 11 pour des metaheuristiques alternatives |

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

## Ponts inter-series

| Serie | Lien | Relation |
| ------- | ------ | ---------- |
| [Partie 2 : CSP](../Part2-CSP/README.md) | Programmation par contraintes | Suite naturelle : recherche declarative |
| [Applications](../Applications/README.md) | 21 notebooks d'application | Mise en pratique des algorithmes |
| [Search (parent)](../README.md) | Vue d'ensemble | Contexte et parcours global |
| [Sudoku](../../Sudoku/) | Resolution par contraintes | Application DLX et CSP |
| [SymbolicAI/Z3](../../SymbolicAI/) | Search-10 (SymbolicAutomata) | Automates + solveur SMT |
| [GameTheory](../../GameTheory/) | Jeux combinatoires | MCTS et theorie des jeux |

## Navigation

[<- Retour a la serie Search](../README.md) | [Partie 2 : CSP ->](../Part2-CSP/README.md) | [Applications ->](../Applications/README.md)

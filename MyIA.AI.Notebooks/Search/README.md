# Search - Algorithmes de Recherche et Programmation par Contraintes

Cette serie explore les algorithmes de recherche et d'optimisation, de la formalisation des espaces d'etats a la programmation par contraintes, en passant par les metaheuristiques. Elle combine **fondements theoriques** et **applications du monde reel** adaptees de projets etudiants EPITA, EPF et ECE.

## Vue d'ensemble

| Partie | Notebooks | Duree |
|--------|-----------|-------|
| Partie 1: Search Fondamental | 11 | ~12h30 |
| Partie 2: Programmation par Contraintes | 9 | ~9h |
| Applications | 20 | ~13h20 |
| **Total** | **40** | **~34h50** |

| Statistique | Valeur |
|-------------|--------|
| Langages | Python (principal), C# (side tracks) |
| Niveau | Debutant a avance |

---

## Partie 1 : Search Fondamental (`Part1-Foundations/`)

Algorithmes de recherche classiques, recherche adversariale et metaheuristiques.

| # | Notebook | Duree | Contenu | Prerequis |
|---|----------|-------|---------|-----------|
| 1 | [Search-1-StateSpace](Part1-Foundations/Search-1-StateSpace.ipynb) | ~40 min | Espaces d'etats, formalisation (S, A, T, G), taquin, aspirateur, route | Python basique |
| 2 | [Search-2-Uninformed](Part1-Foundations/Search-2-Uninformed.ipynb) | ~50 min | BFS, DFS, UCS, IDDFS, comparaison systematique | Search-1 |
| 3 | [Search-3-Informed](Part1-Foundations/Search-3-Informed.ipynb) | ~50 min | A*, Greedy, IDA*, heuristiques admissibles et consistantes | Search-2 |
| 4 | [Search-4-LocalSearch](Part1-Foundations/Search-4-LocalSearch.ipynb) | ~45 min | Hill Climbing, Simulated Annealing, Tabu Search, paysages de fitness | Search-2 |
| 5 | [Search-5-GeneticAlgorithms](Part1-Foundations/Search-5-GeneticAlgorithms.ipynb) | ~50 min | Selection, crossover, mutation, DEAP/PyGAD, theorie unifiee | Search-4 |
| 6 | [Search-6-AdversarialSearch](Part1-Foundations/Search-6-AdversarialSearch.ipynb) | ~1h | Minimax, Alpha-Beta pruning, Null-window search, Transposition tables | Search-2, Search-3 |
| 7 | [Search-7-MCTS-And-Beyond](Part1-Foundations/Search-7-MCTS-And-Beyond.ipynb) | ~1h30 | MCTS, UCB1, OpenSpiel, AlphaGo-style (DQN+MCTS) | Search-6 |
| 8 | [Search-8-DancingLinks](Part1-Foundations/Search-8-DancingLinks.ipynb) | ~1h30 | Algorithme X, DLX, Sudoku, N-Queens, Pentominoes | Search-2 |
| 9 | [Search-9-LinearProgramming](Part1-Foundations/Search-9-LinearProgramming.ipynb) | ~2h | PuLP, simplex, transport, diet, sensibilite, PLNE | Algebre lineaire |
| 10 | [Search-10-SymbolicAutomata](Part1-Foundations/Search-10-SymbolicAutomata.ipynb) | ~2h | DFA/NFA (automata-lib), predicats Z3, automates symboliques | Search-1, SymbolicAI/Z3 |
| 11 | [Search-11-Metaheuristics](Part1-Foundations/Search-11-Metaheuristics.ipynb) | ~1h30 | PSO, ABC, SA, BRO avec MEALPy, benchmark comparatif | Search-4, Search-5 |

---

## Partie 2 : Programmation par Contraintes (`Part2-CSP/`)

> **Pivot vers SymbolicAI** : Z3, Planning, Logic. Cette partie fait le pont entre les algorithmes de recherche et l'IA symbolique.

| # | Notebook | Duree | Contenu | Prerequis |
|---|----------|-------|---------|-----------|
| 1 | [CSP-1-Fundamentals](Part2-CSP/CSP-1-Fundamentals.ipynb) | ~50 min | Variables, domaines, contraintes, backtracking, MRV, LCV | Search-1, Search-2 |
| 2 | [CSP-2-Consistency](Part2-CSP/CSP-2-Consistency.ipynb) | ~45 min | AC-3, Forward checking, MAC, propagation de contraintes | CSP-1 |
| 3 | [CSP-3-Advanced](Part2-CSP/CSP-3-Advanced.ipynb) | ~50 min | AllDifferent, cumulative, circuit, symetries, LNS | CSP-2 |
| 4 | [CSP-4-Scheduling](Part2-CSP/CSP-4-Scheduling.ipynb) | ~1h | Job-Shop (JSSP), RCPSP, Nurse Scheduling, IntervalVar, NoOverlap, Cumulative | CSP-3 |
| 5 | [CSP-5-Optimization](Part2-CSP/CSP-5-Optimization.ipynb) | ~1h | Bin Packing, Knapsack, Cutting Stock, Portfolio Optimization, cardinalite | CSP-3, Search-9 |
| 6 | [CSP-6-Hybridization](Part2-CSP/CSP-6-Hybridization.ipynb) | ~1h30 | Lazy Clause Generation (LCG), CP+SAT, CP+ML, LLM+CSP, parallelisation | CSP-4, CSP-5 |
| 7 | [CSP-7-Soft](Part2-CSP/CSP-7-Soft.ipynb) | ~1h | Contraintes souples, Fuzzy CSP, Weighted CSP, Semiring-based CSP | CSP-1, CSP-2 |
| 8 | [CSP-8-Temporal](Part2-CSP/CSP-8-Temporal.ipynb) | ~1h | Allen's Interval Algebra, STP, TCSP, raisonnement temporel | CSP-1, CSP-2 |
| 9 | [CSP-9-Distributed](Part2-CSP/CSP-9-Distributed.ipynb) | ~1h30 | Asynchronous Backtracking (ABT), AWC, Privacy-preserving CSP | CSP-1, CSP-2, CSP-6 |

### Prerequis CSP

Les notebooks CSP necessitent une comprehension prealable de :
- **Search-1 (StateSpace)** : formalisation des problemes
- **Search-2 (Uninformed)** : backtracking = DFS avec retour arriere

---

## Applications (`Applications/`)

Problemes du monde reel adaptes de projets etudiants (EPITA PPC 2025, EPF MSMIN5IN52, ECE Ing4 2026).

### Applications Search (`Applications/Search/`)

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-12-ConnectFour](Applications/Search/App-12-ConnectFour.ipynb) | ~50 min | Puissance 4 : 8 algorithmes IA (Minimax, MCTS, DQN-RL) | EPITA PPC 2025 |
| 2 | [App-14-ConnectFour-Adversarial](Applications/Search/App-14-ConnectFour-Adversarial.ipynb) | ~45 min | Benchmark adversarial : Minimax, Alpha-Beta, MCTS | ECE 2026 + EPITA |

### Applications CSP (`Applications/CSP/`)

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-1-NQueens](Applications/CSP/App-1-NQueens.ipynb) | ~30 min | Benchmark classique CSP : backtracking, min-conflicts, OR-Tools | Classique |
| 2 | [App-2-GraphColoring](Applications/CSP/App-2-GraphColoring.ipynb) | ~45 min | Coloration de cartes : Greedy, DSATUR, CP-SAT, departements francais | ECE 2026 Gr01 |
| 3 | [App-3-NurseScheduling](Applications/CSP/App-3-NurseScheduling.ipynb) | ~60 min | Planning infirmiers : contraintes hard/soft, OR-Tools CP-SAT | EPITA PPC 2025 |
| 4 | [App-4-JobShopScheduling](Applications/CSP/App-4-JobShopScheduling.ipynb) | ~60 min | Ordonnancement industriel : intervalles, precedences, makespan | EPITA PPC 2025 |
| 5 | [App-5-Timetabling](Applications/CSP/App-5-Timetabling.ipynb) | ~50 min | Emploi du temps universitaire : MiniZinc + OR-Tools | EPITA PPC 2025 |
| 6 | [App-6-Minesweeper](Applications/CSP/App-6-Minesweeper.ipynb) | ~50 min | Demineur CSP : propagation, probabilites, hybride CSP+LLM | EPITA PPC 2025 |
| 7 | [App-7-Wordle](Applications/CSP/App-7-Wordle.ipynb) | ~45 min | Solveur Wordle : filtrage CSP + theorie de l'information | EPITA PPC 2025 |
| 8 | [App-8-MiniZinc](Applications/CSP/App-8-MiniZinc.ipynb) | ~50 min | Modelisation declarative : syntaxe MiniZinc, contraintes globales | Nouveau |
| 9 | [App-11-Picross](Applications/CSP/App-11-Picross.ipynb) | ~40 min | Nonogrammes : speedup 27Mx CP-SAT vs naive | EPITA PPC 2025 |
| 10 | [App-15-SportsScheduling](Applications/CSP/App-15-SportsScheduling.ipynb) | ~55 min | Calendrier sportif : contraintes TV, equite, deplacements | ECE 2026 |
| 11 | [App-16-Crossword-CSP](Applications/CSP/App-16-Crossword-CSP.ipynb) | ~45 min | Mots croises : backtracking, OR-Tools, generation | EPF 2025 |

### Applications Hybrides / Metaheuristiques (`Applications/Hybrid/`)

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-9-EdgeDetection](Applications/Hybrid/App-9-EdgeDetection.ipynb) | ~40 min | Detection de bords par GA : PyGAD, filtres de convolution | Existant (refonte) |
| 2 | [App-9b-EdgeDetection-CSharp](Applications/Hybrid/App-9b-EdgeDetection-CSharp.ipynb) | ~35 min | Side track C# : GeneticSharp pour detection de bords | Existant |
| 3 | [App-10-Portfolio](Applications/Hybrid/App-10-Portfolio.ipynb) | ~40 min | Optimisation de portefeuille : frontiere de Pareto, multi-objectif | Existant (refonte) |
| 4 | [App-10b-Portfolio-CSharp](Applications/Hybrid/App-10b-Portfolio-CSharp.ipynb) | ~30 min | Side track C# : GeneticSharp pour portefeuille | Existant |
| 5 | [App-13-TSP-Metaheuristics](Applications/Hybrid/App-13-TSP-Metaheuristics.ipynb) | ~50 min | TSP : SA, GA, ACO, OR-Tools routing | Classique |
| 6 | [App-17-VRP-Logistics](Applications/Hybrid/App-17-VRP-Logistics.ipynb) | ~60 min | Vehicle Routing : SA, GA, ACO, CP-SAT | EPF 2025 |
| 7 | [App-18-HyperparameterTuning](Applications/Hybrid/App-18-HyperparameterTuning.ipynb) | ~40 min | Optimisation ML : Bayesienne, GA, PSO, Optuna | Nouveau |

---

## Navigation entre sous-series

```text
Part1-Foundations/              Part2-CSP/                  Applications/
Search-1  StateSpace     ───>  CSP-1  Fundamentals   ───>  App-1 NQueens, App-2 GraphColoring
Search-2  Uninformed     ───>  CSP-2  Consistency    ───>  App-6 Minesweeper, App-7 Wordle
Search-3  Informed       ───>  Search-6 Adversarial  ───>  App-12 ConnectFour
       │                        CSP-3  Advanced      ───>  App-3 NurseScheduling, App-4 JobShop
       │                        CSP-4  Scheduling    ───>  App-3, App-4, App-5 Timetabling
       └──> Search-6 (Adversarial)
                │
                └──> Search-7 (MCTS)

Search-4  LocalSearch           CSP-5  Optimization  ───>  App-10 Portfolio
    │                               │
    └──> Search-5 (Genetic)    CSP-6  Hybridization ───>  LLM+CSP
            │                       │
            └──> Search-11 (Meta)   └──> Applications/Hybrid/ App-9 EdgeDetection

Search-8  Dancing Links    ───>  App-11 Picross, Sudoku-5 DLX
Search-9  Linear Programming ─>  CSP-5 Optimization   ───>  App-10 Portfolio
Search-10 Symbolic Automata ─>  Sudoku-12 Automates symboliques
```

### Transition vers SymbolicAI

```text
Part2-CSP                      SymbolicAI/
CSP-3  Advanced (OR-Tools) ───> Linq2Z3 (SMT solving)
CSP-4  Scheduling          ───> Planners (PDDL, HTN, Temporal)
CSP-6  Hybridization       ───> LLM+CSP, Tweety (Formal Logic)
CSP-8  Temporal            ───> Temporal Planning, STP
```

---

## Liens avec les autres series

| Serie | Lien |
|-------|------|
| [Sudoku](../Sudoku/README.md) | Application complete des CSP (17 solveurs dont DLX et automates symboliques) |
| [SymbolicAI](../SymbolicAI/README.md) | Z3 SMT, OR-Tools, planification PDDL, automates symboliques |
| [GameTheory](../GameTheory/README.md) | Minimax, MCTS (jeux a information parfaite) |
| [Probas/Infer](../Probas/README.md) | Approches probabilistes des CSP |
| [GenAI](../GenAI/README.md) | Optimisation d'hyperparametres avec metaheuristiques |

---

## Prerequis

### Python

```bash
# Creer un environnement
python -m venv venv
# Ou: conda create -n search python=3.10

# Installer les dependances
pip install -r requirements.txt
```

### C# (.NET Interactive) - pour side tracks uniquement

```bash
# .NET 9.0 requis
dotnet --version

# Les packages NuGet sont installes dans les notebooks :
# - GeneticSharp
# - SkiaSharp (visualisation)
```

### MiniZinc (optionnel, pour App-8)

```bash
# Installer MiniZinc IDE depuis https://www.minizinc.org/
# Puis: pip install minizinc
```

---

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Espace d'etats** | Formalisation (S, s0, A, T, G) d'un probleme de recherche |
| **BFS/DFS/A*** | Algorithmes de recherche non informee et informee |
| **Heuristique** | Fonction h(n) estimant le cout restant (f = g + h pour A*) |
| **Recherche locale** | Hill Climbing, Simulated Annealing, Tabu Search |
| **Recherche adversariale** | Minimax, Alpha-Beta pruning, Null-window search |
| **MCTS** | Monte Carlo Tree Search : Selection, Expansion, Simulation, Backpropagation |
| **Metaheuristiques** | PSO, ABC, SA, BRO - optimisation sans derivees |
| **CSP** | Constraint Satisfaction Problem : (X, D, C) |
| **Backtracking** | Exploration systematique avec retour arriere |
| **MRV/LCV** | Heuristiques de choix de variable/valeur |
| **Arc Consistency** | Reduction des domaines par propagation (AC-3) |
| **Algorithme Genetique** | Evolution de population : selection, crossover, mutation |
| **Dancing Links (DLX)** | Algorithme X avec listes doublement liees pour couverture exacte |
| **Programmation Lineaire** | Optimisation lineaire avec contraintes (PuLP, simplex) |
| **Automates Symboliques** | Predicats Z3 pour alphabets infinis |
| **OR-Tools CP-SAT** | Solveur de programmation par contraintes de Google |

---

## Ressources

### Livres de reference

- [AIMA - Russell & Norvig (4th ed.)](http://aima.cs.berkeley.edu/) - Chapitres 3-6
- [Constraint Processing - Rina Dechter (2003)](https://www.cambridge.org/core/books/constraint-processing/)
- [Handbook of Constraint Programming (2006)](https://www.elsevier.com/books/handbook-of-constraint-programming/)
- [The CP-SAT Primer (2023)](https://pganalyze.com/blog/cp-sat-primer) - Guide pratique OR-Tools

### Bibliotheques

- [Google OR-Tools](https://developers.google.com/optimization) - Solveur CP-SAT
- [python-constraint](https://pypi.org/project/python-constraint/) - CSP basique
- [Z3 Theorem Prover](https://github.com/Z3Prover/z3) - Solveur SMT
- [DEAP](https://deap.readthedocs.io/) - Framework GA
- [PyGAD](https://pygad.readthedocs.io/) - GA simplifie
- [MEALPy](https://github.com/thieu1995/mealpy) - Metaheuristiques (160+ algorithmes)
- [PuLP](https://github.com/coin-or/pulp) - Programmation lineaire
- [automata-lib](https://pypi.org/project/automata-lib/) - Automates finis
- [MiniZinc](https://www.minizinc.org/) - Modelisation declarative
- [GeneticSharp](https://github.com/giacomelli/GeneticSharp) - GA en C#
- [OpenSpiel](https://github.com/deepmind/open_spiel) - Framework de jeux et RL

### Projets etudiants sources

- [EPITA PPC 2025](https://github.com/jsboigeEpita/2025-Epita-Programmation-par-Contraintes) - 25 projets CSP
- [EPF MSMIN5IN52 2025](https://github.com/jsboigeEPF/2025-MSMIN5IN52-Search-Symbolic-Min1) - 18 projets Search/Symbolic
- [ECE Ing4 2026](https://github.com/jsboigeECE/2026-ECE-Ing4-Fin-IA-Projet1-Gr01) - 15 projets IA exploratoire

---

## Structure des fichiers

```text
Search/
├── README.md                              # Ce fichier
├── requirements.txt                       # Dependances Python
├── search_helpers.py                      # Utilitaires partages
├── resources/                             # Images et donnees
│
├── Part1-Foundations/                     # Search Fondamental (11 notebooks)
│   ├── Search-1-StateSpace.ipynb
│   ├── Search-2-Uninformed.ipynb
│   ├── Search-3-Informed.ipynb
│   ├── Search-4-LocalSearch.ipynb
│   ├── Search-5-GeneticAlgorithms.ipynb
│   ├── Search-6-AdversarialSearch.ipynb
│   ├── Search-7-MCTS-And-Beyond.ipynb
│   ├── Search-8-DancingLinks.ipynb
│   ├── Search-9-LinearProgramming.ipynb
│   ├── Search-10-SymbolicAutomata.ipynb
│   └── Search-11-Metaheuristics.ipynb
│
├── Part2-CSP/                             # Programmation par Contraintes (9 notebooks)
│   ├── CSP-1-Fundamentals.ipynb
│   ├── CSP-2-Consistency.ipynb
│   ├── CSP-3-Advanced.ipynb
│   ├── CSP-4-Scheduling.ipynb
│   ├── CSP-5-Optimization.ipynb
│   ├── CSP-6-Hybridization.ipynb
│   ├── CSP-7-Soft.ipynb
│   ├── CSP-8-Temporal.ipynb
│   └── CSP-9-Distributed.ipynb
│
├── Applications/
│   ├── Search/                            # Applications Search (2 notebooks)
│   │   ├── App-12-ConnectFour.ipynb
│   │   └── App-14-ConnectFour-Adversarial.ipynb
│   │
│   ├── CSP/                               # Applications CSP (11 notebooks)
│   │   ├── App-1-NQueens.ipynb
│   │   ├── App-2-GraphColoring.ipynb
│   │   ├── App-3-NurseScheduling.ipynb
│   │   ├── App-4-JobShopScheduling.ipynb
│   │   ├── App-5-Timetabling.ipynb
│   │   ├── App-6-Minesweeper.ipynb
│   │   ├── App-7-Wordle.ipynb
│   │   ├── App-8-MiniZinc.ipynb
│   │   ├── App-11-Picross.ipynb
│   │   ├── App-15-SportsScheduling.ipynb
│   │   └── App-16-Crossword-CSP.ipynb
│   │
│   └── Hybrid/                            # Metaheuristiques (7 notebooks)
│       ├── App-9-EdgeDetection.ipynb
│       ├── App-9b-EdgeDetection-CSharp.ipynb
│       ├── App-10-Portfolio.ipynb
│       ├── App-10b-Portfolio-CSharp.ipynb
│       ├── App-13-TSP-Metaheuristics.ipynb
│       ├── App-17-VRP-Logistics.ipynb
│       └── App-18-HyperparameterTuning.ipynb
│
├── Foundations/                           # (deprecated) Ancien repertoire
│   └── README.md
│
├── CSPs_Intro.ipynb                       # Ancien notebook (conserve)
├── Exploration_non_informee_*.ipynb       # Anciens notebooks (conerves)
├── GeneticSharp-EdgeDetection.ipynb       # Ancien notebook (conserve)
├── Portfolio_Optimization_GeneticSharp.ipynb # Ancien notebook (conserve)
└── PyGad-EdgeDetection.ipynb              # Ancien notebook (conserve)
```

---

## Licence

Voir la licence du repository principal.

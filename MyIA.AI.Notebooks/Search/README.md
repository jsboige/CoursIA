# Search - Algorithmes de Recherche et Programmation par Contraintes

Cette serie explore les algorithmes de recherche et d'optimisation, de la formalisation des espaces d'etats a la programmation par contraintes, en passant par les metaheuristiques. Elle combine **fondements theoriques** et **applications du monde reel** adaptees de projets etudiants EPITA, EPF et ECE.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | ~24 (Foundations: 12, Applications: 12) |
| Langages | Python (principal), C# (side tracks) |
| Duree estimee | ~22h |
| Niveau | Debutant a avance |

## Structure

La serie est organisee en **deux sous-series** complementaires :

### Partie 1 : Fondations algorithmiques (`Foundations/`)

Progression theorique des espaces d'etats aux CSP avances.

| # | Notebook | Duree | Contenu | Prerequis |
|---|----------|-------|---------|-----------|
| 1 | [Search-1-StateSpace](Foundations/Search-1-StateSpace.ipynb) | ~40 min | Espaces d'etats, formalisation (S, A, T, G), taquin, aspirateur, route | Python basique |
| 2 | [Search-2-Uninformed](Foundations/Search-2-Uninformed.ipynb) | ~50 min | BFS, DFS, UCS, IDDFS, comparaison systematique | Search-1 |
| 3 | [Search-3-Informed](Foundations/Search-3-Informed.ipynb) | ~50 min | A*, Greedy, IDA*, heuristiques admissibles et consistantes | Search-2 |
| 4 | [Search-4-LocalSearch](Foundations/Search-4-LocalSearch.ipynb) | ~45 min | Hill Climbing, Simulated Annealing, Tabu Search, paysages de fitness | Search-2 |
| 5 | [Search-5-GeneticAlgorithms](Foundations/Search-5-GeneticAlgorithms.ipynb) | ~50 min | Selection, crossover, mutation, DEAP/PyGAD, theorie unifiee | Search-4 |
| 6 | [Search-6-CSP-Fundamentals](Foundations/Search-6-CSP-Fundamentals.ipynb) | ~50 min | Variables, domaines, contraintes, backtracking, MRV, LCV | Search-1 |
| 7 | [Search-7-CSP-Consistency](Foundations/Search-7-CSP-Consistency.ipynb) | ~45 min | AC-3, Forward checking, MAC, propagation de contraintes | Search-6 |
| 8 | [Search-8-CSP-Advanced](Foundations/Search-8-CSP-Advanced.ipynb) | ~50 min | AllDifferent, cumulative, circuit, symetries, LNS | Search-7 |
| 9 | [Search-9-Metaheuristics](Foundations/Search-9-Metaheuristics.ipynb) | ~1h30 | PSO, ABC, SA, BRO avec MEALPy, benchmark comparatif | Search-4, Search-5 |
| 10 | [Search-10-DancingLinks](Foundations/Search-10-DancingLinks.ipynb) | ~1h30 | Algorithme X, DLX, Sudoku, N-Queens, Pentominoes | Search-2 |
| 11 | [Search-11-LinearProgramming](Foundations/Search-11-LinearProgramming.ipynb) | ~2h | PuLP, simplex, transport, diet, sensibilite, PLNE | Algebre lineaire |
| 12 | [Search-12-SymbolicAutomata](Foundations/Search-12-SymbolicAutomata.ipynb) | ~2h | DFA/NFA (automata-lib), predicats Z3, automates symboliques | Search-1, SymbolicAI/Z3 |

### Partie 2 : Applications (`Applications/`)

Problemes du monde reel adaptes de projets etudiants (EPITA PPC 2025, EPF MSMIN5IN52, ECE Ing4 2026).

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-1-NQueens](Applications/App-1-NQueens.ipynb) | ~30 min | Benchmark classique CSP : backtracking, min-conflicts, OR-Tools | Classique |
| 2 | [App-2-GraphColoring](Applications/App-2-GraphColoring.ipynb) | ~45 min | Coloration de cartes : Greedy, DSATUR, CP-SAT, departements francais | ECE 2026 Gr01 |
| 3 | [App-3-NurseScheduling](Applications/App-3-NurseScheduling.ipynb) | ~60 min | Planning infirmiers : contraintes hard/soft, OR-Tools CP-SAT | EPITA PPC 2025 |
| 4 | [App-4-JobShopScheduling](Applications/App-4-JobShopScheduling.ipynb) | ~60 min | Ordonnancement industriel : intervalles, precedences, makespan | EPITA PPC 2025 |
| 5 | [App-5-Timetabling](Applications/App-5-Timetabling.ipynb) | ~50 min | Emploi du temps universitaire : MiniZinc + OR-Tools | EPITA PPC 2025 |
| 6 | [App-6-Minesweeper](Applications/App-6-Minesweeper.ipynb) | ~50 min | Demineur CSP : propagation, probabilites, hybride CSP+LLM | EPITA PPC 2025 |
| 7 | [App-7-Wordle](Applications/App-7-Wordle.ipynb) | ~45 min | Solveur Wordle : filtrage CSP + theorie de l'information | EPITA PPC 2025 |
| 8 | [App-8-MiniZinc](Applications/App-8-MiniZinc.ipynb) | ~50 min | Modelisation declarative : syntaxe MiniZinc, contraintes globales | Nouveau |
| 9 | [App-9-EdgeDetection](Applications/App-9-EdgeDetection.ipynb) | ~40 min | Detection de bords par GA : PyGAD, filtres de convolution | Existant (refonte) |
| 9b | [App-9b-EdgeDetection-CSharp](Applications/App-9b-EdgeDetection-CSharp.ipynb) | ~35 min | Side track C# : GeneticSharp pour detection de bords | Existant |
| 10 | [App-10-Portfolio](Applications/App-10-Portfolio.ipynb) | ~40 min | Optimisation de portefeuille : frontiere de Pareto, multi-objectif | Existant (refonte) |
| 10b | [App-10b-Portfolio-CSharp](Applications/App-10b-Portfolio-CSharp.ipynb) | ~30 min | Side track C# : GeneticSharp pour portefeuille | Existant |

### Notebooks bonus (projets etudiants exceptionnels)

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 11 | [App-11-Picross](Applications/App-11-Picross.ipynb) | ~40 min | Nonogrammes : speedup 27Mx CP-SAT vs naive | EPITA PPC 2025 |
| 12 | [App-12-ConnectFour](Applications/App-12-ConnectFour.ipynb) | ~50 min | Puissance 4 : 8 algorithmes IA (Minimax, MCTS, DQN-RL) | EPITA PPC 2025 |

## Navigation entre sous-series

```
Foundations/                    Applications/
Search-1  StateSpace       ──>  App-1  NQueens
Search-2  Uninformed            App-2  GraphColoring
Search-3  Informed              App-3  NurseScheduling
Search-4  LocalSearch      ──>  App-4  JobShopScheduling
Search-5  GeneticAlgorithms ──> App-9  EdgeDetection, App-10 Portfolio
Search-6  CSP Fundamentals ──>  App-1  NQueens, App-2 GraphColoring
Search-7  CSP Consistency  ──>  App-6  Minesweeper, App-7 Wordle
Search-8  CSP Advanced     ──>  App-3  NurseScheduling, App-4 JobShop, App-8 MiniZinc
Search-9  Metaheuristics    ──>  Benchmark optimisation continue
Search-10 Dancing Links    ──>  App-11 Picross, Sudoku-5 DLX
Search-11 Linear Programming─>  App-10 Portfolio optimisation
Search-12 Symbolic Automata─>  Sudoku-12 Automata symboliques
```

## Liens avec les autres series

| Serie | Lien |
|-------|------|
| [Sudoku](../Sudoku/README.md) | Application complete des CSP (17 solveurs dont DLX et automates symboliques) |
| [SymbolicAI](../SymbolicAI/README.md) | Z3 SMT, OR-Tools, planification PDDL, automates symboliques |
| [GameTheory](../GameTheory/README.md) | Minimax, MCTS (jeux a information parfaite) |
| [Probas/Infer](../Probas/README.md) | Approches probabilistes des CSP |
| [GenAI](../GenAI/README.md) | Optimisation d'hyperparametres avec metaheuristiques |

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

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Espace d'etats** | Formalisation (S, s0, A, T, G) d'un probleme de recherche |
| **BFS/DFS/A*** | Algorithmes de recherche non informee et informee |
| **Heuristique** | Fonction h(n) estimant le cout restant (f = g + h pour A*) |
| **Recherche locale** | Hill Climbing, Simulated Annealing, Tabu Search |
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

### Projets etudiants sources
- [EPITA PPC 2025](https://github.com/jsboigeEpita/2025-Epita-Programmation-par-Contraintes) - 25 projets CSP
- [EPF MSMIN5IN52 2025](https://github.com/jsboigeEPF/2025-MSMIN5IN52-Search-Symbolic-Min1) - 18 projets Search/Symbolic
- [ECE Ing4 2026](https://github.com/jsboigeECE/2026-ECE-Ing4-Fin-IA-Projet1-Gr01) - 15 projets IA exploratoire

## Structure des fichiers

```
Search/
├── README.md                              # Ce fichier
├── requirements.txt                       # Dependances Python
├── search_helpers.py                      # Utilitaires partages
├── resources/                             # Images et donnees
│
├── Foundations/                            # Sous-serie 1 : Fondations (12 notebooks)
│   ├── README.md
│   ├── Search-1-StateSpace.ipynb
│   ├── Search-2-Uninformed.ipynb
│   ├── Search-3-Informed.ipynb
│   ├── Search-4-LocalSearch.ipynb
│   ├── Search-5-GeneticAlgorithms.ipynb
│   ├── Search-6-CSP-Fundamentals.ipynb
│   ├── Search-7-CSP-Consistency.ipynb
│   ├── Search-8-CSP-Advanced.ipynb
│   ├── Search-9-Metaheuristics.ipynb
│   ├── Search-10-DancingLinks.ipynb
│   ├── Search-11-LinearProgramming.ipynb
│   └── Search-12-SymbolicAutomata.ipynb
│
├── Applications/                           # Sous-serie 2 : Applications
│   ├── README.md
│   ├── App-1-NQueens.ipynb
│   ├── App-2-GraphColoring.ipynb
│   ├── App-3-NurseScheduling.ipynb
│   ├── App-4-JobShopScheduling.ipynb
│   ├── App-5-Timetabling.ipynb
│   ├── App-6-Minesweeper.ipynb
│   ├── App-7-Wordle.ipynb
│   ├── App-8-MiniZinc.ipynb
│   ├── App-9-EdgeDetection.ipynb
│   ├── App-9b-EdgeDetection-CSharp.ipynb
│   ├── App-10-Portfolio.ipynb
│   └── App-10b-Portfolio-CSharp.ipynb
│
├── CSPs_Intro.ipynb                        # Ancien notebook (conserve, remplace par Search-6/7)
├── Exploration_non_informee_*.ipynb        # Ancien notebook (conserve, remplace par Search-2/3/4)
├── GeneticSharp-EdgeDetection.ipynb        # Ancien notebook (conserve, base pour App-9b)
├── Portfolio_Optimization_GeneticSharp.ipynb # Ancien notebook (conserve, base pour App-10b)
└── PyGad-EdgeDetection.ipynb               # Ancien notebook (conserve, base pour App-9)
```

## Licence

Voir la licence du repository principal.

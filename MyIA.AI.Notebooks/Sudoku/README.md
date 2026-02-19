# Sudoku - Resolution par Differentes Approches Algorithmiques

Cette serie de **23 notebooks** explore differentes techniques de resolution de Sudoku, des algorithmes classiques aux approches symboliques, probabilistes et neuronales. Les notebooks sont disponibles en deux versions : **C# (.NET Interactive)** et **Python**.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 23 (19 C#, 4 Python) |
| Duree estimee | ~6h |
| Niveau | Debutant a avance |
| Langages | C# (.NET Interactive), Python |

## Progression Pedagogique

La serie suit une **progression de complexite des approches IA** en 7 niveaux :

```
Niveau 1 : Recherche Exhaustive
    └── Backtracking (DFS simple, garanti)

Niveau 2 : Exploration Optimisee
    └── Dancing Links (couverture exacte, optimisation du backtracking)

Niveau 3 : Metaheuristiques (exploration non exhaustive)
    ├── Algorithme Genetique
    ├── Recuit Simule
    └── PSO (NOUVEAU)

Niveau 4 : Programmation par Contraintes (CSP)
    ├── AIMA CSP (NOUVEAU - reference academique)
    ├── Propagation de Norvig (MRV + Forward Checking)
    ├── Strategies Humaines (13 techniques d'inference)
    ├── Graph Coloring (NOUVEAU - formulation graphe du CSP)
    ├── OR-Tools CP-SAT (bibliotheque industrielle)
    └── Choco Solver (NOUVEAU - autre bibliotheque CP)

Niveau 5 : IA Symbolique (SMT, Automates)
    ├── Z3 SMT Solver
    ├── Automates Symboliques + Z3
    └── BDD/MDD (diagrammes de decision)

Niveau 6 : IA Moderne / Data-Driven
    ├── Infer.NET (probabiliste)
    ├── Reseaux de Neurones (CNN)
    └── LLM Solver (NOUVEAU - unique!)

Niveau 7 : Synthese
    └── Benchmark Comparatif
```

## Structure

### Notebooks C# (.NET Interactive)

| # | Notebook | Niveau | Duree | Contenu | Prerequis |
|---|----------|--------|-------|---------|-----------|
| 0 | [Sudoku-0-Environment](Sudoku-0-Environment.ipynb) | Base | ~6 min | Classes de base `SudokuGrid`, `ISudokuSolver` | .NET 9.0 |
| 1 | [Sudoku-1-Backtracking](Sudoku-1-Backtracking.ipynb) | Recherche | ~7 min | DFS exhaustif, garanti | Sudoku-0 |
| 2 | [Sudoku-2-DancingLinks](Sudoku-2-DancingLinks.ipynb) | Exploration | ~9 min | Algorithme X de Knuth, couverture exacte | Sudoku-0 |
| 3 | [Sudoku-3-Genetic](Sudoku-3-Genetic.ipynb) | Metaheuristique | ~14 min | GeneticSharp, chromosomes | Sudoku-0 |
| 4 | [Sudoku-4-SimulatedAnnealing](Sudoku-4-SimulatedAnnealing.ipynb) | Metaheuristique | ~20 min | Recuit simule : energie, refroidissement | Sudoku-0 |
| 5 | Sudoku-5-PSO | Metaheuristique | ~20 min | Particle Swarm Optimization | Sudoku-0 |
| 6 | Sudoku-6-AIMA-CSP | CSP | ~25 min | Reference academique : AC-3, Forward Checking | Sudoku-0 |
| 7 | [Sudoku-7-Norvig](Sudoku-7-Norvig.ipynb) | CSP | ~20 min | Propagation : elimination, naked/hidden singles | Sudoku-0 |
| 8 | [Sudoku-8-HumanStrategies](Sudoku-8-HumanStrategies.ipynb) | CSP | ~25 min | 13 strategies humaines : X-Wing, Y-Wing, etc. | Sudoku-0 |
| 9 | Sudoku-9-GraphColoring | CSP | ~15 min | Formulation coloration de graphe, DSATUR | Sudoku-0 |
| 10 | [Sudoku-10-ORTools](Sudoku-10-ORTools.ipynb) | CSP | ~11 min | CP Solver, SAT Solver, MIP avec Google OR-Tools | Sudoku-0 |
| 11 | Sudoku-11-Choco | CSP | ~15 min | Solveur Choco, comparaison d'heuristiques | Sudoku-0 |
| 12 | [Sudoku-12-Z3](Sudoku-12-Z3.ipynb) | Symbolique | ~13 min | Microsoft Z3, solveurs entiers et bitvectors | Sudoku-0 |
| 13 | [Sudoku-13-SymbolicAutomata](Sudoku-13-SymbolicAutomata.ipynb) | Symbolique | ~30 min | Automates symboliques compiles vers SMT (Z3) | Sudoku-0 |
| 14 | [Sudoku-14-BDD](Sudoku-14-BDD.ipynb) | Symbolique | ~25 min | Binary Decision Diagrams (approche pure) | Sudoku-13 |
| 15 | [Sudoku-15-Infer](Sudoku-15-Infer.ipynb) | Data-Driven | ~19 min | Modeles graphiques probabilistes avec Infer.NET | Sudoku-0 |
| 16 | [Sudoku-16-NeuralNetwork](Sudoku-16-NeuralNetwork.ipynb) | Data-Driven | ~25 min | 4 architectures CNN avec PyTorch | Python, DL |
| 17 | Sudoku-17-LLM | Data-Driven | ~20 min | Solveur LLM avec Semantic Kernel | Sudoku-0 |
| 18 | [Sudoku-18-Comparison](Sudoku-18-Comparison.ipynb) | Synthese | ~20 min | Benchmark comparatif final de tous les solveurs | Python |

### Notebooks Python (annexes)

| Notebook | Duree | Contenu |
|----------|-------|---------|
| [Sudoku-Python-Backtracking](Sudoku-Python-Backtracking.ipynb) | ~11 min | Backtracking + MRV, visualisation matplotlib |
| [Sudoku-Python-Genetic](Sudoku-Python-Genetic.ipynb) | ~10 min | Algorithme genetique avec PyGAD |
| [Sudoku-Python-DancingLinks](Sudoku-Python-DancingLinks.ipynb) | ~13 min | Dancing Links from scratch |
| [Sudoku-Python-ORTools-Z3](Sudoku-Python-ORTools-Z3.ipynb) | ~10 min | OR-Tools CP-SAT, Z3 SMT, comparaison |

## Algorithmes Couverts

| Algorithme | Type | Performance | Fiabilite | Notebook |
|------------|------|-------------|-----------|----------|
| **Backtracking** | Recherche exhaustive | Rapide (Easy) | Garantie | 1 |
| **Dancing Links** | Couverture exacte | Optimal | Garantie | 2 |
| **Algorithme Genetique** | Metaheuristique | Variable | Non garanti | 3 |
| **Recuit Simule** | Recherche locale | Variable | Non garanti | 4 |
| **PSO** | Swarm Intelligence | Variable | Non garanti | 5 (NOUVEAU) |
| **AIMA CSP** | Contraintes academique | Rapide | Garantie | 6 (NOUVEAU) |
| **Norvig Propagation** | Propagation | Tres rapide | Garantie | 7 |
| **Strategies Humaines** | Deduction logique | Variable | Partielle | 8 |
| **Graph Coloring** | Theorie des graphes | Moyen | Garantie | 9 (NOUVEAU) |
| **OR-Tools CP-SAT** | CP industrielle | Tres rapide | Garantie | 10 |
| **Choco Solver** | CP industrielle | Rapide | Garantie | 11 (NOUVEAU) |
| **Z3 SMT** | Satisfiabilite | Rapide | Garantie | 12 |
| **Symbolic Automata** | Automates + SMT | Rapide | Garantie | 13 |
| **BDD/MDD** | Diagrammes decision | Moyen | Garantie | 14 |
| **Infer.NET** | Inference probabiliste | Experimental | Variable | 15 |
| **Reseau de Neurones** | Deep Learning | Rapide (inference) | Approx. | 16 |
| **LLM Solver** | LLM | Variable | ~10-30% | 17 (NOUVEAU) |

## Progression recommandee

```
Sudoku-0  Environment (classes de base)
    |
    +---> Niveau 1 : Recherche Exhaustive
    |     └── Sudoku-1  Backtracking
    |
    +---> Niveau 2 : Exploration Optimisee
    |     └── Sudoku-2  Dancing Links
    |
    +---> Niveau 3 : Metaheuristiques
    |     ├── Sudoku-3  Genetic
    |     ├── Sudoku-4  Simulated Annealing
    |     └── Sudoku-5  PSO (NOUVEAU)
    |
    +---> Niveau 4 : Programmation par Contraintes
    |     ├── Sudoku-6  AIMA CSP (NOUVEAU)
    |     ├── Sudoku-7  Norvig
    |     ├── Sudoku-8  Human Strategies
    |     ├── Sudoku-9  Graph Coloring (NOUVEAU)
    |     ├── Sudoku-10 OR-Tools
    |     └── Sudoku-11 Choco (NOUVEAU)
    |
    +---> Niveau 5 : IA Symbolique
    |     ├── Sudoku-12 Z3
    |     ├── Sudoku-13 Symbolic Automata
    |     └── Sudoku-14 BDD
    |
    +---> Niveau 6 : IA Moderne
    |     ├── Sudoku-15 Infer.NET
    |     ├── Sudoku-16 Neural Network
    |     └── Sudoku-17 LLM (NOUVEAU)
    |
    +---> Niveau 7 : Synthese
          └── Sudoku-18 Comparison
```

## Liens avec les autres series

| Serie | Lien |
|-------|------|
| [Search - Foundations](../Search/Foundations/README.md) | Theorie : backtracking, propagation, CP avance |
| [Search - Applications](../Search/Applications/README.md) | Autres problemes CSP : N-Queens, Minesweeper, Wordle |
| [SymbolicAI](../SymbolicAI/README.md) | Z3 SMT (approfondi), OR-Tools |
| [Probas/Infer](../Probas/README.md) | Infer.NET (approfondi) |
| [GameTheory](../GameTheory/README.md) | Minimax, MCTS (jeux combinatoires) |

## Prerequis

### C# (.NET Interactive)

```bash
# .NET 9.0 requis
dotnet --version

# Les packages NuGet sont installes dans les notebooks :
# - GeneticSharp
# - Google.OrTools
# - Microsoft.Z3
# - DlxLib
# - Microsoft.ML.Probabilistic
# - Microsoft.SemanticKernel (pour LLM)
# - Plotly.NET
```

**Note sur les outputs** : Les notebooks C# (.NET Interactive) ne contiennent pas de outputs de cellule executes. L'infrastructure Jupyter pour .NET n'etant pas disponible dans tous les environnements, les notebooks sont fournis sans outputs pre-executes.

### Python

```bash
# Creer un environnement
python -m venv venv

# Installer les dependances
pip install numpy matplotlib ortools z3-solver pygad torch
```

## Performances Attendues

| Solveur | Easy | Medium | Hard | Expert |
|---------|------|--------|------|--------|
| Backtracking | <10ms | ~100ms | ~1s | Variable |
| Dancing Links | <2ms | <5ms | <15ms | <50ms |
| Norvig | <2ms | <5ms | <10ms | <30ms |
| OR-Tools | <1ms | <5ms | <10ms | <50ms |
| Z3 | <5ms | <10ms | <20ms | <100ms |
| Genetic | ~1s | ~10s | Non garanti | Non garanti |
| Simulated Annealing | ~2s | ~5s | Variable | Variable |
| PSO | ~1s | ~5s | Variable | Variable |
| Human Strategies | <10ms | ~100ms | Variable | Variable |
| Choco | <5ms | <10ms | <20ms | <100ms |
| Neural Network | ~10ms | ~50ms | ~100ms | Approx. |
| LLM | Variable | Variable | ~10-30% succes | ~10-30% succes |
| Infer.NET | ~1s | ~5s | Variable | Variable |

## Sources des projets etudiants

Les notebooks sont adaptes des meilleurs projets etudiants des depots GitHub :

| Technique | Source | Repertoire |
|-----------|--------|------------|
| **Norvig** | [jsboigeEpita/2024-Sudoku-NLP](https://github.com/jsboigeEpita/2024-EPITA-SCIA-PPC-Sudoku-NLP) | `Sudoku.Norvig` + `Sudoku.NorvigBitArray` |
| **Simulated Annealing** | [jsboigeEpita/2023-Sudoku-NLP](https://github.com/jsboigeEpita/2023-EPITA-SCIA-PPC-Sudoku-NLP) | `Sudoku.SimulatedAnnealing` |
| **Human Strategies** | [jsboigeEpita/2024-Sudoku-NLP](https://github.com/jsboigeEpita/2024-EPITA-SCIA-PPC-Sudoku-NLP) | `Sudoku.Human` (23 fichiers, 13 techniques) |
| **Neural Network** | [jsboigeEpita/2024-Sudoku-CV](https://github.com/jsboigeEpita/2024-EPITA-SCIA-PPC-Sudoku-CV) | `Sudoku.NeuralNetwork` (4 architectures) |
| **PSO** | [jsboige/MSMIN4IN32-22-MIN2-Sudoku](https://github.com/jsboige/MSMIN4IN32-22-MIN2-Sudoku) | `Sudoku.PSO` (7 fichiers) |
| **AIMA CSP** | [jsboigeEpita/2024-Sudoku-NLP](https://github.com/jsboigeEpita/2024-EPITA-SCIA-PPC-Sudoku-NLP) | `Sudoku.CspAima` |
| **Graph Coloring** | [jsboige/MSMIN4IN32-22-MIN2-Sudoku](https://github.com/jsboige/MSMIN4IN32-22-MIN2-Sudoku) | `Sodoku.GraphColoring` (11 fichiers) |
| **Choco** | [jsboigeECE/2025-Sudoku-Gr01](https://github.com/jsboigeECE/2025-ECE-Ing4-Fin-Sudoku-Gr01) | `Sudoku.ChocoSolvers` (5 implementations) |
| **LLM** | [jsboigeECE/2025-Sudoku-Gr01](https://github.com/jsboigeECE/2025-ECE-Ing4-Fin-Sudoku-Gr01) | `Sudoku.LLM-ChatGPTenzin` |

## Structure des Fichiers

```
Sudoku/
├── README.md                              # Ce fichier
├── Sudoku-0-Environment.ipynb             # Classes de base C#
├── Sudoku-1-Backtracking.ipynb            # Backtracking C#
├── Sudoku-2-DancingLinks.ipynb            # Dancing Links C#
├── Sudoku-3-Genetic.ipynb                 # Algorithme genetique C#
├── Sudoku-4-SimulatedAnnealing.ipynb      # Recuit simule C#
├── Sudoku-5-PSO.ipynb                     # PSO C# (NOUVEAU)
├── Sudoku-6-AIMA-CSP.ipynb                # AIMA CSP C# (NOUVEAU)
├── Sudoku-7-Norvig.ipynb                  # Propagation de Norvig C#
├── Sudoku-8-HumanStrategies.ipynb         # Strategies humaines C#
├── Sudoku-9-GraphColoring.ipynb           # Graph Coloring C# (NOUVEAU)
├── Sudoku-10-ORTools.ipynb                # OR-Tools C#
├── Sudoku-11-Choco.ipynb                  # Choco Solver C# (NOUVEAU)
├── Sudoku-12-Z3.ipynb                     # Z3 SMT C#
├── Sudoku-13-SymbolicAutomata.ipynb       # Automates symboliques C#
├── Sudoku-14-BDD.ipynb                    # BDD/MDD C#
├── Sudoku-15-Infer.ipynb                  # Infer.NET C#
├── Sudoku-16-NeuralNetwork.ipynb          # Reseau de neurones Python
├── Sudoku-17-LLM.ipynb                    # LLM Solver C# (NOUVEAU)
├── Sudoku-18-Comparison.ipynb             # Benchmark comparatif Python
├── Sudoku-Python-Backtracking.ipynb       # Backtracking Python
├── Sudoku-Python-Genetic.ipynb            # Algorithme genetique Python
├── Sudoku-Python-DancingLinks.ipynb       # Dancing Links Python
├── Sudoku-Python-ORTools-Z3.ipynb         # OR-Tools + Z3 Python
└── Puzzles/                               # Fichiers de puzzles
    ├── Sudoku_Easy51.txt
    ├── Sudoku_hardest.txt
    └── Sudoku_top95.txt
```

## Ressources

### Livres et articles
- [Peter Norvig - Solving Every Sudoku Puzzle (2006)](http://norvig.com/sudoku.html)
- [Donald Knuth - Dancing Links (2000)](https://arxiv.org/abs/cs/0011047)
- [Russell & Norvig - Artificial Intelligence: A Modern Approach (CSP Chapter)](https://aima.cs.berkeley.edu/)

### Bibliotheques
- [OR-Tools Documentation](https://developers.google.com/optimization)
- [Z3 Python API](https://z3prover.github.io/api/html/namespacez3py.html)
- [GeneticSharp](https://github.com/giacomelli/GeneticSharp)
- [Choco Solver](https://choco-solver.org/)
- [Infer.NET Documentation](https://dotnet.github.io/infer/)
- [Microsoft Semantic Kernel](https://learn.microsoft.com/en-us/semantic-kernel/)
- [PyTorch](https://pytorch.org/)

## Licence

Voir la licence du repository principal.

# Sudoku - Résolution par Différentes Approches Algorithmiques

Cette série de **30 notebooks** explore différentes techniques de résolution de Sudoku, des algorithmes classiques aux approches symboliques, probabilistes et neuronales. Les notebooks sont disponibles en **approche miroir C#/Python** pour permettre aux étudiants de choisir leur langage.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 30 (15 C#, 15 Python) |
| Durée estimée | ~8h |
| Niveau | Débutant à avancé |
| Langages | C# (.NET Interactive), Python |

## Progression Pédagogique

La série suit une **progression de complexité des approches IA** en 7 niveaux :

```
Niveau 1 : Recherche Exhaustive
    └── Backtracking (DFS simple, garanti)

Niveau 2 : Exploration Optimisée
    └── Dancing Links (couverture exacte, optimisation du backtracking)

Niveau 3 : Metaheuristiques (exploration non exhaustive)
    ├── Algorithme Génétique
    ├── Recuit Simulé
    └── PSO

Niveau 4 : Programmation par Contraintes (CSP)
    ├── AIMA CSP (référence académique)
    ├── Propagation de Norvig (MRV + Forward Checking)
    ├── Stratégies Humaines (13 techniques d'inférence)
    ├── Graph Coloring (formulation graphe du CSP)
    ├── OR-Tools CP-SAT (bibliothèque industrielle)
    └── Choco Solver (autre bibliothèque CP)

Niveau 5 : IA Symbolique (SMT, Automates)
    ├── Z3 SMT Solver
    ├── Automates Symboliques + Z3
    └── BDD/MDD (diagrammes de décision)

Niveau 6 : IA Moderne / Data-Driven
    ├── Infer.NET (probabiliste)
    ├── Réseaux de Neurones (CNN)
    └── LLM Solver

Niveau 7 : Synthèse
    └── Benchmark Comparatif
```

## Structure des Notebooks

| # | Sujet | C# | Python | Technologie Python |
|---|-------|----|----|-------------------|
| 0 | Environment | ✓ | - | - |
| 1 | Backtracking | ✓ | ✓ | Backtracking + MRV |
| 2 | Dancing Links | ✓ | ✓ | Algorithm X from scratch |
| 3 | Genetic | ✓ | ✓ | PyGAD |
| 4 | Simulated Annealing | ✓ | - | `simanneal` (à créer) |
| 5 | PSO | ✓ | - | `mealpy` (à créer) |
| 6 | AIMA CSP | ✓ | - | Port Russell & Norvig (à créer) |
| 7 | Norvig | ✓ | - | Original Norvig (à créer) |
| 8 | Human Strategies | ✓ | - | Port C#→Python (à créer) |
| 9 | Graph Coloring | ✓ | ✓ | **networkx** + `nx.sudoku_graph()` |
| 10 | OR-Tools | ✓ | ✓ | **ortools** CP-SAT |
| 11 | Choco | - | ✓ | **JPype** + Choco JAR |
| 12 | Z3 | ✓ | ✓ | **z3-solver** |
| 13 | Symbolic Automata | ✓ | - | (C# uniquement) |
| 14 | BDD | ✓ | - | (C# uniquement) |
| 15 | Infer.NET | ✓ | - | (C# uniquement) |
| 16 | Neural Network | - | ✓ | **PyTorch** CNN |
| 17 | LLM | - | ✓ | **Semantic Kernel** |
| 18 | Comparison | - | ✓ | Benchmark comparatif |

**Légende** : ✓ = disponible, - = non applicable ou à créer

## Notebooks avec Versions Miroir C#/Python

Les notebooks suivants sont disponibles dans les deux langages pour comparaison directe :

| # | Sujet | C# | Python | Intérêt pédagogique |
|---|-------|----|----|-------------------|
| 1 | Backtracking | [Sudoku-1-Backtracking-Csharp](Sudoku-1-Backtracking-Csharp.ipynb) | [Sudoku-1-Backtracking-Python](Sudoku-1-Backtracking-Python.ipynb) | Algorithme de base |
| 2 | Dancing Links | [Sudoku-2-DancingLinks-Csharp](Sudoku-2-DancingLinks-Csharp.ipynb) | [Sudoku-2-DancingLinks-Python](Sudoku-2-DancingLinks-Python.ipynb) | Couverture exacte |
| 3 | Genetic | [Sudoku-3-Genetic-Csharp](Sudoku-3-Genetic-Csharp.ipynb) | [Sudoku-3-Genetic-Python](Sudoku-3-Genetic-Python.ipynb) | GeneticSharp vs PyGAD |
| 9 | Graph Coloring | [Sudoku-9-GraphColoring-Csharp](Sudoku-9-GraphColoring-Csharp.ipynb) | [Sudoku-9-GraphColoring-Python](Sudoku-9-GraphColoring-Python.ipynb) | Théorie des graphes |
| 10 | OR-Tools | [Sudoku-10-ORTools-Csharp](Sudoku-10-ORTools-Csharp.ipynb) | [Sudoku-10-ORTools-Python](Sudoku-10-ORTools-Python.ipynb) | CP-SAT solveur |
| 12 | Z3 | [Sudoku-12-Z3-Csharp](Sudoku-12-Z3-Csharp.ipynb) | [Sudoku-12-Z3-Python](Sudoku-12-Z3-Python.ipynb) | SMT solveur |

## Algorithmes Couverts

| Algorithme | Type | Performance | Fiabilité | Notebook C# | Notebook Python |
|------------|------|-------------|-----------|-------------|-----------------|
| **Backtracking** | Recherche exhaustive | Rapide (Easy) | Garantie | 1 | 1 |
| **Dancing Links** | Couverture exacte | Optimal | Garantie | 2 | 2 |
| **Algorithme Génétique** | Metaheuristique | Variable | Non garanti | 3 | 3 |
| **Recuit Simulé** | Recherche locale | Variable | Non garanti | 4 | - |
| **PSO** | Swarm Intelligence | Variable | Non garanti | 5 | - |
| **AIMA CSP** | Contraintes académique | Rapide | Garantie | 6 | - |
| **Norvig Propagation** | Propagation | Très rapide | Garantie | 7 | - |
| **Stratégies Humaines** | Déduction logique | Variable | Partielle | 8 | - |
| **Graph Coloring** | Théorie des graphes | Moyen | Garantie | 9 | 9 |
| **OR-Tools CP-SAT** | CP industrielle | Très rapide | Garantie | 10 | 10 |
| **Choco Solver** | CP industrielle | Rapide | Garantie | - | 11 |
| **Z3 SMT** | Satisfiabilité | Rapide | Garantie | 12 | 12 |
| **Symbolic Automata** | Automates + SMT | Rapide | Garantie | 13 | - |
| **BDD/MDD** | Diagrammes décision | Moyen | Garantie | 14 | - |
| **Infer.NET** | Inference probabiliste | Expérimental | Variable | 15 | - |
| **Réseau de Neurones** | Deep Learning | Rapide (inference) | Approx. | - | 16 |
| **LLM Solver** | LLM | Variable | ~10-30% | - | 17 |

## Progression Recommandée

### Parcours C# (Complet)
```
Sudoku-0-Csharp (Environment)
    |
    +---> Niveau 1 : Sudoku-1-Backtracking-Csharp
    |
    +---> Niveau 2 : Sudoku-2-DancingLinks-Csharp
    |
    +---> Niveau 3 : Sudoku-3/4/5-Csharp (Metaheuristiques)
    |
    +---> Niveau 4 : Sudoku-6/7/8/9/10-Csharp (CSP)
    |
    +---> Niveau 5 : Sudoku-12/13/14-Csharp (Symbolique)
    |
    +---> Niveau 6 : Sudoku-15-Csharp (Infer.NET)
    |
    +---> Niveau 7 : Sudoku-18-Comparison-Python (Benchmark)
```

### Parcours Python (Sélection)
```
Sudoku-0-Csharp (Environment - même en Python)
    |
    +---> Niveau 1 : Sudoku-1-Backtracking-Python
    |
    +---> Niveau 2 : Sudoku-2-DancingLinks-Python
    |
    +---> Niveau 3 : Sudoku-3-Genetic-Python
    |
    +---> Niveau 4 : Sudoku-9/10/11/12-Python (CSP)
    |
    +---> Niveau 6 : Sudoku-16/17-Python (NN + LLM)
    |
    +---> Niveau 7 : Sudoku-18-Comparison-Python
```

## Liens avec les autres séries

| Série | Lien |
|-------|------|
| [Search - Foundations](../Search/Foundations/README.md) | Théorie : backtracking, propagation, CP avancé |
| [Search - Applications](../Search/Applications/README.md) | Autres problèmes CSP : N-Queens, Minesweeper, Wordle |
| [SymbolicAI](../SymbolicAI/README.md) | Z3 SMT (approfondi), OR-Tools |
| [Probas/Infer](../Probas/README.md) | Infer.NET (approfondi) |
| [GameTheory](../GameTheory/README.md) | Minimax, MCTS (jeux combinatoires) |

## Prérequis

### C# (.NET Interactive)

```bash
# .NET 9.0 requis
dotnet --version

# Les packages NuGet sont installés dans les notebooks :
# - GeneticSharp
# - Google.OrTools
# - Microsoft.Z3
# - DlxLib
# - Microsoft.ML.Probabilistic
# - Microsoft.SemanticKernel (pour LLM)
# - Plotly.NET
```

**Note sur les outputs** : Les notebooks C# (.NET Interactive) ne contiennent pas de outputs de cellule exécutées.

### Python

```bash
# Créer un environnement
python -m venv venv

# Installer les dépendances
pip install numpy matplotlib ortools z3-solver pygad torch networkx
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
| Graph Coloring | ~10ms | ~50ms | ~100ms | Variable |
| Neural Network | ~10ms | ~50ms | ~100ms | Approx. |
| LLM | Variable | Variable | ~10-30% succès | ~10-30% succès |
| Infer.NET | ~1s | ~5s | Variable | Variable |

## Sources des Projets Étudiants

Les notebooks sont adaptés des meilleurs projets étudiants des dépôts GitHub :

| Technique | Source | Répertoire |
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
├── Sudoku-0-Environment-Csharp.ipynb      # Classes de base C#
├── Sudoku-1-Backtracking-Csharp.ipynb     # Backtracking C#
├── Sudoku-1-Backtracking-Python.ipynb     # Backtracking Python
├── Sudoku-2-DancingLinks-Csharp.ipynb     # Dancing Links C#
├── Sudoku-2-DancingLinks-Python.ipynb     # Dancing Links Python
├── Sudoku-3-Genetic-Csharp.ipynb          # Algorithme génétique C#
├── Sudoku-3-Genetic-Python.ipynb          # Algorithme génétique Python
├── Sudoku-4-SimulatedAnnealing-Csharp.ipynb  # Recuit simulé C#
├── Sudoku-5-PSO-Csharp.ipynb              # PSO C#
├── Sudoku-6-AIMA-CSP-Csharp.ipynb         # AIMA CSP C#
├── Sudoku-7-Norvig-Csharp.ipynb           # Propagation de Norvig C#
├── Sudoku-8-HumanStrategies-Csharp.ipynb  # Stratégies humaines C#
├── Sudoku-9-GraphColoring-Csharp.ipynb    # Graph Coloring C#
├── Sudoku-9-GraphColoring-Python.ipynb    # Graph Coloring Python (networkx)
├── Sudoku-10-ORTools-Csharp.ipynb         # OR-Tools C#
├── Sudoku-10-ORTools-Python.ipynb         # OR-Tools Python
├── Sudoku-11-Choco-Python.ipynb           # Choco Solver Python
├── Sudoku-12-Z3-Csharp.ipynb              # Z3 SMT C#
├── Sudoku-12-Z3-Python.ipynb              # Z3 SMT Python
├── Sudoku-13-SymbolicAutomata-Csharp.ipynb # Automates symboliques C#
├── Sudoku-14-BDD-Csharp.ipynb             # BDD/MDD C#
├── Sudoku-15-Infer-Csharp.ipynb           # Infer.NET C#
├── Sudoku-16-NeuralNetwork-Python.ipynb   # Réseau de neurones Python
├── Sudoku-17-LLM-Python.ipynb             # LLM Solver Python
├── Sudoku-18-Comparison-Python.ipynb      # Benchmark comparatif Python
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

### Bibliothèques
- [OR-Tools Documentation](https://developers.google.com/optimization)
- [Z3 Python API](https://z3prover.github.io/api/html/namespacez3py.html)
- [NetworkX](https://networkx.org/) - Graphes et algorithmes de coloration
- [GeneticSharp](https://github.com/giacomelli/GeneticSharp)
- [Choco Solver](https://choco-solver.org/)
- [Infer.NET Documentation](https://dotnet.github.io/infer/)
- [Microsoft Semantic Kernel](https://learn.microsoft.com/en-us/semantic-kernel/)
- [PyTorch](https://pytorch.org/)

## Licence

Voir la licence du repository principal.

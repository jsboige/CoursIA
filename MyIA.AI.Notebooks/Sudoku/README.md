# Sudoku - Resolution par Differentes Approches Algorithmiques

Cette serie de **18 notebooks** explore differentes techniques de resolution de Sudoku, des algorithmes classiques aux approches symboliques, probabilistes et neuronales. Les notebooks sont disponibles en deux versions : **C# (.NET Interactive)** et **Python**.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 18 (10 C#, 8 Python) |
| Duree estimee | ~5h |
| Niveau | Debutant a avance |
| Langages | C# (.NET Interactive), Python |

## Structure

### Notebooks C# (.NET Interactive)

| # | Notebook | Duree | Contenu | Prerequis |
|---|----------|-------|---------|-----------|
| 0 | [Sudoku-0-Environment](Sudoku-0-Environment.ipynb) | ~6 min | Classes de base `SudokuGrid`, `ISudokuSolver`, `SudokuHelper` | .NET 9.0 |
| 1 | [Sudoku-1-Backtracking](Sudoku-1-Backtracking.ipynb) | ~7 min | Algorithme de backtracking simple, recherche en profondeur | Sudoku-0 |
| 2 | [Sudoku-2-Genetic](Sudoku-2-Genetic.ipynb) | ~14 min | GeneticSharp, chromosomes par cellules et permutations | Sudoku-0 |
| 3 | [Sudoku-3-ORTools](Sudoku-3-ORTools.ipynb) | ~11 min | CP Solver, SAT Solver, MIP avec Google OR-Tools | Sudoku-0 |
| 4 | [Sudoku-4-Z3](Sudoku-4-Z3.ipynb) | ~13 min | Microsoft Z3, solveurs entiers et bitvectors | Sudoku-0 |
| 5 | [Sudoku-5-DancingLinks](Sudoku-5-DancingLinks.ipynb) | ~9 min | Algorithme X de Knuth, couverture exacte | Sudoku-0 |
| 6 | [Sudoku-6-Infer](Sudoku-6-Infer.ipynb) | ~19 min | Modeles graphiques probabilistes avec Infer.NET | Sudoku-0 |
| 7 | [Sudoku-7-Norvig](Sudoku-7-Norvig.ipynb) | ~20 min | Propagation de Norvig : elimination, naked/hidden singles | Sudoku-0 |
| 8 | [Sudoku-8-SimulatedAnnealing](Sudoku-8-SimulatedAnnealing.ipynb) | ~20 min | Recuit simule : energie, refroidissement, swaps | Sudoku-0 |
| 9 | [Sudoku-9-HumanStrategies](Sudoku-9-HumanStrategies.ipynb) | ~25 min | 13 strategies humaines : X-Wing, Naked Pairs, Locked Candidates | Sudoku-0 |
| 12 | [Sudoku-12-SymbolicAutomata](Sudoku-12-SymbolicAutomata.ipynb) | ~30 min | Automates symboliques avec CharSet et Z3 (vrais SFA) | Sudoku-0 |

### Notebooks Python

| # | Notebook | Duree | Contenu | Prerequis |
|---|----------|-------|---------|-----------|
| - | [Sudoku-Python-Backtracking](Sudoku-Python-Backtracking.ipynb) | ~11 min | Backtracking + MRV, visualisation matplotlib | Python |
| - | [Sudoku-Python-ORTools-Z3](Sudoku-Python-ORTools-Z3.ipynb) | ~10 min | OR-Tools CP-SAT, Z3 SMT, comparaison performances | Python |
| - | [Sudoku-Python-Genetic](Sudoku-Python-Genetic.ipynb) | ~10 min | Algorithme genetique avec PyGAD | Python |
| - | [Sudoku-Python-DancingLinks](Sudoku-Python-DancingLinks.ipynb) | ~13 min | Dancing Links from scratch | Python |
| 10 | [Sudoku-10-NeuralNetwork](Sudoku-10-NeuralNetwork.ipynb) | ~25 min | 4 architectures CNN (Dense, Conv, iteratif) avec PyTorch | Python, DL basique |
| 11 | [Sudoku-11-Comparison](Sudoku-11-Comparison.ipynb) | ~20 min | Benchmark comparatif final de tous les solveurs | Python |

## Progression recommandee

```
Sudoku-0  Environment (classes de base)
    |
    +---> Sudoku-1  Backtracking (recherche exhaustive)
    |         |
    |         +---> Sudoku-7  Norvig (propagation de contraintes)
    |         |
    |         +---> Sudoku-9  Human Strategies (13 techniques)
    |
    +---> Sudoku-2  Genetic (metaheuristique)
    |         |
    |         +---> Sudoku-8  Simulated Annealing (recherche locale)
    |
    +---> Sudoku-3  OR-Tools (programmation par contraintes)
    |
    +---> Sudoku-4  Z3 (SMT)
    |
    +---> Sudoku-12  Symbolic Automata (Z3, automates symboliques)
    |
    +---> Sudoku-5  Dancing Links (couverture exacte)
    |
    +---> Sudoku-6  Infer.NET (inference probabiliste)
    |
    +---> Sudoku-10  Neural Network (deep learning)
    |
    +---> Sudoku-11  Comparison (benchmark final)
```

## Algorithmes Couverts

| Algorithme | Type | Performance | Fiabilite | Notebook |
|------------|------|-------------|-----------|----------|
| **Backtracking** | Recherche exhaustive | Rapide (Easy) | Garantie | 1 |
| **Backtracking + MRV** | Heuristique | Plus stable | Garantie | 1, Python |
| **Algorithme Genetique** | Metaheuristique | Variable | Non garanti | 2, Python |
| **OR-Tools CP-SAT** | Programmation par contraintes | Tres rapide | Garantie | 3, Python |
| **Z3 SMT** | Satisfiabilite Modulo Theories | Rapide | Garantie | 4, Python |
| **Z3 Symbolic Automata (C#)** | Automates symboliques | Rapide | Garantie | 12 (C#) |
| **Dancing Links** | Couverture exacte | Optimal | Garantie | 5, Python |
| **Infer.NET** | Inference probabiliste | Experimental | Variable | 6 |
| **Norvig Propagation** | Propagation de contraintes | Tres rapide | Garantie | 7 |
| **Recuit Simule** | Recherche locale | Variable | Non garanti | 8 |
| **Strategies Humaines** | Deduction logique | Variable | Partielle | 9 |
| **Reseau de Neurones** | Deep Learning | Rapide (inference) | Approx. | 10 |

## Liens avec les autres series

| Serie | Lien |
|-------|------|
| [Search - Foundations](../Search/Foundations/README.md) | Theorie : backtracking (Search-6), propagation (Search-7), CP avance (Search-8), automates symboliques (Search-12) |
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
# - Plotly.NET
```

### Python

```bash
# Creer un environnement
python -m venv venv
# Ou: conda create -n sudoku python=3.10

# Installer les dependances
pip install numpy matplotlib ortools z3-solver pygad torch
```

## Performances Attendues

| Solveur | Easy | Medium | Hard | Expert |
|---------|------|--------|------|--------|
| Backtracking | <10ms | ~100ms | ~1s | Variable |
| MRV | <5ms | ~50ms | ~500ms | ~2s |
| OR-Tools | <1ms | <5ms | <10ms | <50ms |
| Z3 | <5ms | <10ms | <20ms | <100ms |
| Dancing Links | <2ms | <5ms | <15ms | <50ms |
| Norvig | <2ms | <5ms | <10ms | <30ms |
| Genetic | ~1s | ~10s | Non garanti | Non garanti |
| Simulated Annealing | ~2s | ~5s | Variable | Variable |
| Human Strategies | <10ms | ~100ms | Variable | Variable |
| Infer.NET | ~1s | ~5s | Variable | Variable |
| Neural Network | ~10ms | ~50ms | ~100ms | Approx. |

## Sources des projets etudiants

Les nouveaux notebooks sont adaptes des meilleurs projets etudiants :

- **Norvig** : [jsboigeEpita/2024-Sudoku-NLP](https://github.com/jsboigeEpita/2024-EPITA-SCIA-PPC-Sudoku-NLP) - `Sudoku.Norvig` + `Sudoku.NorvigBitArray`
- **Simulated Annealing** : [jsboigeEpita/2023-Sudoku-NLP](https://github.com/jsboigeEpita/2023-EPITA-SCIA-PPC-Sudoku-NLP) - `Sudoku.SimulatedAnnealing`
- **Human Strategies** : [jsboigeEpita/2024-Sudoku-NLP](https://github.com/jsboigeEpita/2024-EPITA-SCIA-PPC-Sudoku-NLP) - `Sudoku.Human` (23 fichiers, 13 techniques)
- **Neural Network** : [jsboigeEpita/2024-Sudoku-CV](https://github.com/jsboigeEpita/2024-EPITA-SCIA-PPC-Sudoku-CV) - `Sudoku.NeuralNetwork` (4 architectures)

## Structure des Fichiers

```
Sudoku/
├── README.md                              # Ce fichier
├── Sudoku-0-Environment.ipynb             # Classes de base C#
├── Sudoku-1-Backtracking.ipynb            # Backtracking C#
├── Sudoku-2-Genetic.ipynb                 # Algorithme genetique C#
├── Sudoku-3-ORTools.ipynb                 # OR-Tools C#
├── Sudoku-4-Z3.ipynb                      # Z3 SMT C#
├── Sudoku-5-DancingLinks.ipynb            # Dancing Links C#
├── Sudoku-6-Infer.ipynb                   # Infer.NET C#
├── Sudoku-7-Norvig.ipynb                  # Propagation de Norvig C#
├── Sudoku-8-SimulatedAnnealing.ipynb      # Recuit simule C#
├── Sudoku-9-HumanStrategies.ipynb         # Strategies humaines C#
├── Sudoku-10-NeuralNetwork.ipynb          # Reseau de neurones Python
├── Sudoku-11-Comparison.ipynb             # Benchmark comparatif Python
├── Sudoku-12-SymbolicAutomata.ipynb       # Automates symboliques C# (CharSet + Z3)
├── Sudoku-Python-Backtracking.ipynb       # Backtracking Python
├── Sudoku-Python-ORTools-Z3.ipynb         # OR-Tools + Z3 Python
├── Sudoku-Python-Genetic.ipynb            # Algorithme genetique Python
├── Sudoku-Python-DancingLinks.ipynb       # Dancing Links Python
└── Puzzles/                               # Fichiers de puzzles
    ├── Sudoku_Easy51.txt
    ├── Sudoku_hardest.txt
    └── Sudoku_top95.txt
```

## Ressources

### Livres et articles
- [Peter Norvig - Solving Every Sudoku Puzzle (2006)](http://norvig.com/sudoku.html)
- [Donald Knuth - Dancing Links (2000)](https://arxiv.org/abs/cs/0011047)

### Bibliotheques
- [OR-Tools Documentation](https://developers.google.com/optimization)
- [Z3 Python API](https://z3prover.github.io/api/html/namespacez3py.html)
- [GeneticSharp](https://github.com/giacomelli/GeneticSharp)
- [Infer.NET Documentation](https://dotnet.github.io/infer/)
- [PyTorch](https://pytorch.org/)

## Licence

Voir la licence du repository principal.

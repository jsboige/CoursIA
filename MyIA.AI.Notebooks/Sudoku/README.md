# Sudoku - Resolution par Differentes Approches Algorithmiques

Cette serie de **11 notebooks** explore differentes techniques de resolution de Sudoku, des algorithmes classiques aux approches probabilistes. Les notebooks sont disponibles en deux versions : **C# (.NET Interactive)** et **Python**.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 11 (7 C#, 4 Python) |
| Cellules totales | 167 (MD: 90, Code: 77) |
| Duree estimee | ~2h |

## Structure

### Notebooks C# (.NET Interactive)

| # | Notebook | Cellules | Duree | Contenu |
|---|----------|----------|-------|---------|
| 0 | [Sudoku-0-Environment](Sudoku-0-Environment.ipynb) | 8 | ~6 min | Classes de base `SudokuGrid`, `ISudokuSolver`, `SudokuHelper` |
| 1 | [Sudoku-1-Backtracking](Sudoku-1-Backtracking.ipynb) | 9 | ~7 min | Algorithme de backtracking simple, recherche en profondeur |
| 2 | [Sudoku-2-Genetic](Sudoku-2-Genetic.ipynb) | 19 | ~14 min | GeneticSharp, chromosomes par cellules et permutations |
| 3 | [Sudoku-3-ORTools](Sudoku-3-ORTools.ipynb) | 15 | ~11 min | CP Solver, SAT Solver, MIP avec Google OR-Tools |
| 4 | [Sudoku-4-Z3](Sudoku-4-Z3.ipynb) | 17 | ~13 min | Microsoft Z3, solveurs entiers et bitvectors |
| 5 | [Sudoku-5-DancingLinks](Sudoku-5-DancingLinks.ipynb) | 12 | ~9 min | Algorithme X de Knuth, couverture exacte |
| 6 | [Sudoku-6-Infer](Sudoku-6-Infer.ipynb) | 25 | ~19 min | Modeles graphiques probabilistes avec Infer.NET |

### Notebooks Python

| # | Notebook | Cellules | Duree | Contenu |
|---|----------|----------|-------|---------|
| - | [Sudoku-Python-Backtracking](Sudoku-Python-Backtracking.ipynb) | 15 | ~11 min | Backtracking + MRV, visualisation matplotlib |
| - | [Sudoku-Python-ORTools-Z3](Sudoku-Python-ORTools-Z3.ipynb) | 14 | ~10 min | OR-Tools CP-SAT, Z3 SMT, comparaison performances |
| - | [Sudoku-Python-Genetic](Sudoku-Python-Genetic.ipynb) | 14 | ~10 min | Algorithme genetique avec PyGAD |
| - | [Sudoku-Python-DancingLinks](Sudoku-Python-DancingLinks.ipynb) | 19 | ~13 min | Dancing Links from scratch |

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
```

### Python

```bash
# Creer un environnement
conda create -n sudoku python=3.10
conda activate sudoku

# Installer les dependances
pip install numpy matplotlib ortools z3-solver
```

## Algorithmes Couverts

| Algorithme | Type | Complexite | Performance |
|------------|------|------------|-------------|
| **Backtracking** | Recherche exhaustive | O(9^81) pire cas | Rapide sur puzzles faciles |
| **Backtracking + MRV** | Heuristique | Amelioree | Plus stable |
| **Algorithme Genetique** | Metaheuristique | Variable | Non garanti |
| **OR-Tools CP** | Programmation par contraintes | Polynomial | Tres rapide |
| **OR-Tools SAT** | Satisfaction booleenne | NP-complet | Tres rapide |
| **Z3 SMT** | Satisfiabilite Modulo Theories | Decidable | Rapide |
| **Z3 BitVectors** | SMT optimise | Decidable | Tres rapide |
| **Dancing Links** | Couverture exacte | O(c*n) | Optimal |
| **Infer.NET** | Inference probabiliste | Variable | Experimental |

## Concepts Cles

| Concept | Description |
|---------|-------------|
| **Backtracking** | Exploration systematique avec retour arriere |
| **MRV (Minimum Remaining Values)** | Heuristique choisissant la cellule la plus contrainte |
| **Contraintes AllDifferent** | Chaque ligne/colonne/bloc contient 1-9 sans repetition |
| **Couverture exacte** | Probleme de selection de sous-ensembles |
| **Dancing Links** | Structure de donnees pour backtracking efficace |
| **Chromosome** | Representation d'une solution candidate (GA) |
| **Inference bayesienne** | Propagation de probabilites sur variables |

## Structure des Fichiers

```
Sudoku/
├── Sudoku-0-Environment.ipynb    # Classes de base C#
├── Sudoku-1-Backtracking.ipynb   # Backtracking C#
├── Sudoku-2-Genetic.ipynb        # Algorithme genetique C#
├── Sudoku-3-ORTools.ipynb        # OR-Tools C#
├── Sudoku-4-Z3.ipynb             # Z3 SMT C#
├── Sudoku-5-DancingLinks.ipynb   # Dancing Links C#
├── Sudoku-6-Infer.ipynb          # Infer.NET C#
├── Sudoku-Python-Backtracking.ipynb
├── Sudoku-Python-ORTools-Z3.ipynb
├── Sudoku-Python-Genetic.ipynb
├── Sudoku-Python-DancingLinks.ipynb
├── puzzles/                       # Fichiers de puzzles
│   ├── Easy.txt
│   ├── Medium.txt
│   ├── Hard.txt
│   └── Expert.txt
└── README.md
```

## Execution

### Notebooks C#

Les notebooks C# utilisent la directive `#!import` pour partager les classes de base.

```bash
# Ouvrir avec Jupyter ou VS Code avec extension .NET Interactive
jupyter notebook Sudoku-1-Backtracking.ipynb
```

**Note** : Executer d'abord `Sudoku-0-Environment.ipynb` pour definir les classes de base.

### Notebooks Python

```bash
# Execution directe
jupyter notebook Sudoku-Python-Backtracking.ipynb

# Ou execution en mode batch (Papermill)
papermill Sudoku-Python-Backtracking.ipynb output.ipynb
```

## Performances Attendues

| Solveur | Easy | Medium | Hard | Expert |
|---------|------|--------|------|--------|
| Backtracking | <10ms | ~100ms | ~1s | Variable |
| MRV | <5ms | ~50ms | ~500ms | ~2s |
| OR-Tools | <1ms | <5ms | <10ms | <50ms |
| Z3 | <5ms | <10ms | <20ms | <100ms |
| Dancing Links | <2ms | <5ms | <15ms | <50ms |
| Genetic | ~1s | ~10s | Non garanti | Non garanti |
| Infer.NET | ~1s | ~5s | Variable | Variable |

## Ressources

- [OR-Tools Documentation](https://developers.google.com/optimization)
- [Z3 Python API](https://z3prover.github.io/api/html/namespacez3py.html)
- [GeneticSharp](https://github.com/giacomelli/GeneticSharp)
- [Donald Knuth - Dancing Links](https://arxiv.org/abs/cs/0011047)
- [Infer.NET Documentation](https://dotnet.github.io/infer/)

## Licence

Voir la licence du repository principal.

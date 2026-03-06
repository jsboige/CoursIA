# Search - Applications

Sous-serie de **14 notebooks** appliquant les algorithmes de recherche et de programmation par contraintes a des problemes du monde reel. Les notebooks sont desormais organises par categorie technique.

## Structure

```text
Applications/
├── Search/     # Applications purement Search (1 notebook)
├── CSP/        # Applications CSP (9 notebooks)
└── Hybrid/     # Metaheuristiques / GA (4 notebooks)
```

---

## Applications Search (`Search/`)

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-12-ConnectFour](Search/App-12-ConnectFour.ipynb) | ~50 min | Puissance 4 : Minimax, MCTS, DQN-RL | EPITA 2025 |

---

## Applications CSP (`CSP/`)

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-1-NQueens](CSP/App-1-NQueens.ipynb) | ~30 min | Backtracking, Min-Conflicts, OR-Tools | Classique |
| 2 | [App-2-GraphColoring](CSP/App-2-GraphColoring.ipynb) | ~45 min | Greedy, DSATUR, CP-SAT, departements | ECE 2026 |
| 3 | [App-3-NurseScheduling](CSP/App-3-NurseScheduling.ipynb) | ~60 min | Hard/soft constraints, CP-SAT | EPITA 2025 |
| 4 | [App-4-JobShopScheduling](CSP/App-4-JobShopScheduling.ipynb) | ~60 min | Intervalles, precedences, makespan | EPITA 2025 |
| 5 | [App-5-Timetabling](CSP/App-5-Timetabling.ipynb) | ~50 min | MiniZinc + OR-Tools | EPITA 2025 |
| 6 | [App-6-Minesweeper](CSP/App-6-Minesweeper.ipynb) | ~50 min | CSP + probabilites + LLM | EPITA 2025 |
| 7 | [App-7-Wordle](CSP/App-7-Wordle.ipynb) | ~45 min | Filtrage CSP + theorie de l'information | EPITA 2025 |
| 8 | [App-8-MiniZinc](CSP/App-8-MiniZinc.ipynb) | ~50 min | Syntaxe MiniZinc, contraintes globales | Nouveau |
| 9 | [App-11-Picross](CSP/App-11-Picross.ipynb) | ~40 min | Nonogrammes : 27Mx speedup CP-SAT | EPITA 2025 |

---

## Applications Hybrid / Metaheuristiques (`Hybrid/`)

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-9-EdgeDetection](Hybrid/App-9-EdgeDetection.ipynb) | ~40 min | GA pour filtres de convolution | Existant |
| 2 | [App-9b-EdgeDetection-CSharp](Hybrid/App-9b-EdgeDetection-CSharp.ipynb) | ~35 min | GeneticSharp (C#) | Existant |
| 3 | [App-10-Portfolio](Hybrid/App-10-Portfolio.ipynb) | ~40 min | Multi-objectif, frontiere de Pareto | Existant |
| 4 | [App-10b-Portfolio-CSharp](Hybrid/App-10b-Portfolio-CSharp.ipynb) | ~30 min | GeneticSharp (C#) | Existant |

---

## Prerequis par notebook

### Applications Search

| Notebook | Fondations requises |
|----------|--------------------|
| App-12 ConnectFour | Search-3 (A*), Search-4 (LocalSearch) |

### Applications CSP

| Notebook | Fondations requises | Dependances |
|----------|--------------------|-------------|
| App-1 NQueens | CSP-1 (Fundamentals) | - |
| App-2 GraphColoring | CSP-1, CSP-2 | networkx |
| App-3 NurseScheduling | CSP-3, CSP-4 | ortools |
| App-4 JobShopScheduling | CSP-3, CSP-4 | ortools |
| App-5 Timetabling | CSP-3 | minizinc |
| App-6 Minesweeper | CSP-2 (Consistency) | - |
| App-7 Wordle | CSP-1, CSP-2 | - |
| App-8 MiniZinc | CSP-3 | minizinc |
| App-11 Picross | CSP-3, Search-10 (DLX) | ortools |

### Applications Hybrid

| Notebook | Fondations requises | Dependances |
|----------|--------------------|-------------|
| App-9 EdgeDetection | Search-5 (GA) | pygad, scikit-image |
| App-9b EdgeDetection | Search-5 (GA) | GeneticSharp (.NET) |
| App-10 Portfolio | Search-5 (GA), Search-11 (PL) | pygad |
| App-10b Portfolio | Search-5 (GA) | GeneticSharp (.NET) |

---

## Sources des projets etudiants

- **EPITA PPC 2025** : Nurse Rostering, Job-Shop, Minesweeper, Wordle, Picross, Connect Four
- **EPF MSMIN5IN52** : Timetabling (MiniZinc)
- **ECE Ing4 2026** : Graph Coloring

---

## Retour

[<- Retour a la serie Search](../README.md)

# Search - Applications

Sous-serie de **12+ notebooks** appliquant les algorithmes de recherche et de programmation par contraintes a des problemes du monde reel. Plusieurs notebooks sont adaptes de projets etudiants EPITA, EPF et ECE.

## Notebooks

### Applications principales

| # | Notebook | Duree | Domaine | Techniques | Source |
|---|----------|-------|---------|------------|--------|
| 1 | [App-1-NQueens](App-1-NQueens.ipynb) | ~30 min | Combinatoire | Backtracking, Min-Conflicts, OR-Tools | Classique |
| 2 | [App-2-GraphColoring](App-2-GraphColoring.ipynb) | ~45 min | Cartographie | Greedy, DSATUR, CP-SAT | ECE 2026 |
| 3 | [App-3-NurseScheduling](App-3-NurseScheduling.ipynb) | ~60 min | Sante | Hard/soft constraints, CP-SAT | EPITA 2025 |
| 4 | [App-4-JobShopScheduling](App-4-JobShopScheduling.ipynb) | ~60 min | Industrie | Intervalles, precedences, makespan | EPITA 2025 |
| 5 | [App-5-Timetabling](App-5-Timetabling.ipynb) | ~50 min | Education | MiniZinc + OR-Tools | EPITA 2025 |
| 6 | [App-6-Minesweeper](App-6-Minesweeper.ipynb) | ~50 min | Jeux/Puzzles | CSP, probabilites, LLM hybride | EPITA 2025 |
| 7 | [App-7-Wordle](App-7-Wordle.ipynb) | ~45 min | Jeux/Puzzles | CSP + theorie de l'information | EPITA 2025 |
| 8 | [App-8-MiniZinc](App-8-MiniZinc.ipynb) | ~50 min | Modelisation | Syntaxe MiniZinc, contraintes globales | Nouveau |
| 9 | [App-9-EdgeDetection](App-9-EdgeDetection.ipynb) | ~40 min | Vision | GA pour filtres de convolution | Existant |
| 10 | [App-10-Portfolio](App-10-Portfolio.ipynb) | ~40 min | Finance | Multi-objectif, frontiere de Pareto | Existant |

### Side tracks C#

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 9b | [App-9b-EdgeDetection-CSharp](App-9b-EdgeDetection-CSharp.ipynb) | ~35 min | GeneticSharp pour detection de bords |
| 10b | [App-10b-Portfolio-CSharp](App-10b-Portfolio-CSharp.ipynb) | ~30 min | GeneticSharp pour portefeuille |

### Notebooks bonus

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 11 | [App-11-Picross](App-11-Picross.ipynb) | ~40 min | Nonogrammes : demo CP vs naive (27Mx speedup) | EPITA 2025 |
| 12 | [App-12-ConnectFour](App-12-ConnectFour.ipynb) | ~50 min | 8 algorithmes IA compares (Minimax a DQN-RL) | EPITA 2025 |

**Duree totale** : ~8h30

## Prerequis par notebook

Tous les notebooks necessitent les [Fondations](../Foundations/README.md). Prerequis specifiques :

| Notebook | Fondations requises | Dependances supplementaires |
|----------|--------------------|-----------------------------|
| App-1 NQueens | Search-6 (CSP) | - |
| App-2 GraphColoring | Search-6, Search-7 | networkx |
| App-3 NurseScheduling | Search-8 (CSP Advanced) | ortools |
| App-4 JobShopScheduling | Search-4, Search-8 | ortools |
| App-5 Timetabling | Search-8 | minizinc (optionnel) |
| App-6 Minesweeper | Search-7 (Consistency) | - |
| App-7 Wordle | Search-6, Search-7 | - |
| App-8 MiniZinc | Search-8 | minizinc |
| App-9 EdgeDetection | Search-5 (GA) | pygad, scikit-image |
| App-10 Portfolio | Search-5 (GA), Search-11 (PL) | pygad |
| App-11 Picross | Search-10 (DLX) | ortools |
| App-12 ConnectFour | Search-3 (A*), Search-4 | numpy, matplotlib |

## Sources des projets etudiants

Les notebooks d'application sont adaptes des meilleurs projets etudiants identifies par comparaison croisee de 12 depots :

- **EPITA PPC 2025** : Nurse Rostering, Job-Shop, Minesweeper (RDER), Wordle (CSP-Wordle-Solver), Picross, Connect Four
- **EPF MSMIN5IN52** : Crossword Generator, VRP, Timetabling (MiniZinc)
- **ECE Ing4 2026** : Graph Coloring (groupe-15)

# Search - Applications

C'est ici que la série Search se confronte au réel. Les 21 notebooks d'application, pour la plupart adaptés de projets étudiants, prennent les algorithmes des Parties 1 et 2 et les mettent face à des problèmes qui ne se laissent pas faire : planifier les gardes d'un service hospitalier, ordonnancer un atelier, construire un calendrier sportif équitable, router une flotte de véhicules. Trois catégories les organisent — **Search pur** (jeux combinatoires), **CSP** (satisfaction de contraintes) et **Hybride** (métaheuristiques et algorithmes génétiques) — et la plupart sont autonomes, avec des pointeurs vers les prérequis pertinents.

Sous-serie de **21 notebooks** | **~14h05** | Python 3.10+ (`ortools`, `deap`, `mealpy`, `minizinc`, `optuna`)

## Pourquoi cette sous-serie

Un algorithme compris sur un exemple jouet n'est pas encore un algorithme maîtrisé. Les applications servent trois apprentissages que les parties théoriques ne peuvent pas donner. D'abord la confrontation des méthodes : le même problème y est régulièrement résolu plusieurs fois — N-Queens en backtracking, en Min-Conflicts et en OR-Tools ; le TSP en recuit simulé, en génétique, en colonies de fourmis et en solveur de routage — et la comparaison chiffrée vaut tous les discours. Ensuite l'ordre de grandeur : voir un solveur de Picross gagner un facteur de plusieurs millions en passant au CP-SAT imprime durablement ce que « propagation » veut dire. Enfin la modélisation, qui est souvent toute la difficulté : le démineur devient un CSP doublé de probabilités, Wordle un problème de théorie de l'information, la génération procédurale de niveaux un Wave Function Collapse encodé en contraintes — autant de cas où trouver la bonne formulation est l'essentiel du travail.

## Objectifs d'apprentissage

A l'issue de cette sous-serie, vous serez capable de :

1. **Transposer** les algorithmes de Search et CSP vers des problemes reels (logistique, ordonnancement, jeux)
2. **Comparer** les approches (backtracking vs CP-SAT vs metaheuristiques) sur des instances concretes
3. **Evaluer** les compromis performance/qualite entre methodes exactes et approchees

## FAQ / Troubleshooting

| Probleme | Solution |
|----------|----------|
| `ModuleNotFoundError: minizinc` | `pip install minizinc` — necessaire pour App-5 (Timetabling) et App-8 (MiniZinc). Requiert aussi l'installation du solver MiniZinc |
| `ModuleNotFoundError: optuna` | `pip install optuna` — necessaire pour App-18 (Hyperparameter Tuning) |
| `ModuleNotFoundError: pygad` | `pip install pygad` — necessaire pour App-9/10 (EdgeDetection, Portfolio) |
| App-9b/10b (.NET) : kernel non disponible | Installer .NET Interactive : `dotnet tool install --global Microsoft.dotnet-interactive` |
| Certains solveurs sont lents (>30s) | Les instances sont intentionally petites pour le pedagogique. Pour des instances plus grandes, activer les timeouts dans CP-SAT (`model.parameters.max_time_in_seconds`) |

## Structure

```text
Applications/
├── Search/     # Applications purement Search (2 notebooks)
├── CSP/        # Applications CSP (12 notebooks)
└── Hybrid/     # Metaheuristiques / GA (7 notebooks)
```

---

## Applications Search (`Search/`)

Deux notebooks autour du Puissance 4, le banc d'essai idéal de la recherche adversariale : assez simple pour être résolu, assez riche pour départager les approches. Le premier construit les joueurs (Minimax, MCTS, et un agent DQN appris), le second les fait s'affronter en benchmark systématique.

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-12-ConnectFour](Search/App-12-ConnectFour.ipynb) | ~50 min | Puissance 4 : Minimax, MCTS, DQN-RL | Projet etudiant |
| 2 | [App-14-ConnectFour-Adversarial](Search/App-14-ConnectFour-Adversarial.ipynb) | ~45 min | Benchmark adversarial : Minimax, Alpha-Beta, MCTS | Projet etudiant |

---

## Applications CSP (`CSP/`)

Le gros de la sous-série, et un panorama de ce que la programmation par contraintes sait faire dès qu'on sort du manuel : des classiques fondateurs (N-Queens, coloration de graphes) aux problèmes d'ordonnancement réalistes (infirmiers, job-shop, emplois du temps, calendriers sportifs), en passant par des terrains plus inattendus — le démineur qui mêle contraintes et probabilités, Wordle lu comme un problème d'information, le Picross qui sert de leçon de vitesse, et la génération procédurale de niveaux par Wave Function Collapse.

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-1-NQueens](CSP/App-1-NQueens.ipynb) | ~30 min | Backtracking, Min-Conflicts, OR-Tools | Classique |
| 2 | [App-2-GraphColoring](CSP/App-2-GraphColoring.ipynb) | ~45 min | Greedy, DSATUR, CP-SAT, departements | Projet etudiant |
| 3 | [App-3-NurseScheduling](CSP/App-3-NurseScheduling.ipynb) | ~60 min | Hard/soft constraints, CP-SAT | Projet etudiant |
| 4 | [App-4-JobShopScheduling](CSP/App-4-JobShopScheduling.ipynb) | ~60 min | Intervalles, precedences, makespan | Projet etudiant |
| 5 | [App-5-Timetabling](CSP/App-5-Timetabling.ipynb) | ~50 min | MiniZinc + OR-Tools | Projet etudiant |
| 6 | [App-6-Minesweeper](CSP/App-6-Minesweeper.ipynb) | ~50 min | CSP + probabilites + LLM | Projet etudiant |
| 7 | [App-7-Wordle](CSP/App-7-Wordle.ipynb) | ~45 min | Filtrage CSP + theorie de l'information | Projet etudiant |
| 8 | [App-8-MiniZinc](CSP/App-8-MiniZinc.ipynb) | ~50 min | Syntaxe MiniZinc, contraintes globales | Nouveau |
| 9 | [App-11-Picross](CSP/App-11-Picross.ipynb) | ~40 min | Nonogrammes : 27Mx speedup CP-SAT | Projet etudiant |
| 10 | [App-15-SportsScheduling](CSP/App-15-SportsScheduling.ipynb) | ~55 min | Calendrier sportif : contraintes TV, equite, deplacements | Projet etudiant |
| 11 | [App-16-Crossword-CSP](CSP/App-16-Crossword-CSP.ipynb) | ~45 min | Mots croises : backtracking, OR-Tools, generation | Projet etudiant |
| 12 | [App-19-ProceduralGeneration-WFC](CSP/App-19-ProceduralGeneration-WFC.ipynb) | ~45 min | Generation procedurale : Wave Function Collapse via CP-SAT | Projet etudiant |

---

## Applications Hybrid / Metaheuristiques (`Hybrid/`)

Quand l'espace est trop vaste ou l'objectif trop irrégulier pour les méthodes exactes, place aux métaheuristiques : détection de contours et optimisation de portefeuille par algorithmes génétiques (avec leurs doublons C#/GeneticSharp en side-track .NET), TSP et VRP attaqués par quatre méthodes concurrentes, et le réglage d'hyperparamètres ML — où la boucle se referme : on optimise l'optimiseur.

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-9-EdgeDetection](Hybrid/App-9-EdgeDetection.ipynb) | ~40 min | GA pour filtres de convolution | Existant |
| 2 | [App-9b-EdgeDetection-CSharp](Hybrid/App-9b-EdgeDetection-CSharp.ipynb) | ~35 min | GeneticSharp (C#) | Existant |
| 3 | [App-10-Portfolio](Hybrid/App-10-Portfolio.ipynb) | ~40 min | Multi-objectif, frontiere de Pareto | Existant |
| 4 | [App-10b-Portfolio-CSharp](Hybrid/App-10b-Portfolio-CSharp.ipynb) | ~30 min | GeneticSharp (C#) | Existant |
| 5 | [App-13-TSP-Metaheuristics](Hybrid/App-13-TSP-Metaheuristics.ipynb) | ~50 min | TSP : SA, GA, ACO, OR-Tools routing | Classique |
| 6 | [App-17-VRP-Logistics](Hybrid/App-17-VRP-Logistics.ipynb) | ~60 min | Vehicle Routing : SA, GA, ACO, CP-SAT | Projet etudiant |
| 7 | [App-18-HyperparameterTuning](Hybrid/App-18-HyperparameterTuning.ipynb) | ~40 min | Optimisation ML : Bayesienne, GA, PSO, Optuna | Nouveau |

---

## Prerequis par notebook

### Applications Search

| Notebook | Fondations requises |
|----------|--------------------|
| App-12 ConnectFour | Search-3 (A*), Search-4 (LocalSearch) |
| App-14 ConnectFour-Adversarial | Search-3 (Heuristiques), Search-6 (AdversarialSearch) |

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
| App-11 Picross | CSP-3, Search-8 (DLX) | ortools |
| App-15 SportsScheduling | CSP-3, CSP-4 | ortools |
| App-16 Crossword-CSP | CSP-1, CSP-2 | ortools |
| App-19 ProceduralGeneration-WFC | CSP-1, CSP-3 | ortools, numpy, matplotlib |

### Applications Hybrid

| Notebook | Fondations requises | Dependances |
|----------|--------------------|-------------|
| App-9 EdgeDetection | Search-5 (GA) | pygad, scikit-image |
| App-9b EdgeDetection | Search-5 (GA) | GeneticSharp (.NET) |
| App-10 Portfolio | Search-5 (GA), Search-9 (PL) | pygad |
| App-10b Portfolio | Search-5 (GA) | GeneticSharp (.NET) |
| App-13 TSP-Metaheuristics | Search-4, Search-5 | ortools |
| App-17 VRP-Logistics | Search-4, Search-5, CSP-3 | ortools |
| App-18 HyperparameterTuning | Search-4, Search-5 | optuna, scikit-learn |

---

## Origine des projets

La plupart des notebooks d'application sont adaptes de projets etudiants realises dans le cadre de cours d'IA. Les references specifics sont indiquees dans chaque notebook.

---

## Ponts inter-series

| Serie | Lien | Relation |
| ------- | ------ | ---------- |
| [Partie 1 : Search](../Part1-Foundations/README.md) | Fondamentaux | Source des algorithmes utilises |
| [Partie 2 : CSP](../Part2-CSP/README.md) | Programmation par contraintes | Solveurs CP-SAT, MiniZinc |
| [Search (parent)](../README.md) | Vue d'ensemble | Contexte et parcours global |
| [ML/ML.Net](../../ML/ML.Net/) | App-18 (HyperparameterTuning) | Optimisation bayesienne + GA |
| [Sudoku](../../Sudoku/) | App-11 (Picross), App-1 (NQueens) | Problemes combinatoires similaires |
| [GameTheory](../../GameTheory/) | App-12/14 (ConnectFour) | Jeux a deux joueurs, MCTS |

## Navigation

[<- Partie 1 : Search](../Part1-Foundations/README.md) | [Partie 2 : CSP](../Part2-CSP/README.md) | [Retour a la serie Search](../README.md)

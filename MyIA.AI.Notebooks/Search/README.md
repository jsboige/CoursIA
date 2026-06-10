# Search - Algorithmes de Recherche et Programmation par Contraintes

<!-- CATALOG-STATUS
series: Search
pedagogical_count: 46
breakdown: Applications=21, Part1-Foundations=11, Part2-CSP=9, root=5
maturity: PRODUCTION=45, BETA=1
-->

Tout problème d'IA, du plus simple jeu de plateau à la planification logistique industrielle, se réduit à un même défi : explorer un espace de solutions possibles pour trouver la meilleure. Cette série vous apprend à maîtriser cette exploration, depuis les algorithmes classiques (BFS, A*, Minimax) jusqu'aux techniques avancées (CSP, métaheuristiques, hybridation LLM). Le fil rouge est la **réduction de l'espace de recherche** : comment passer d'une exploration aveugle exponentielle à une résolution intelligemment guidée.

Le parcours couvre quatre grands piliers. Les **fondements** formalisent les espaces d'états et couvrent les algorithmes de recherche non informée, informée, locale, génétique, adversariale et MCTS. La **programmation par contraintes** (CSP) introduit un changement de paradigme : au lieu d'explorer, on réduit les domaines par propagation. Les **applications** (20 notebooks) illustrent chaque concept sur des problèmes réels adaptés de projets étudiants. Enfin, les **métaheuristiques et l'hybridation** relient la recherche à l'optimisation continue et aux LLMs.

**46 notebooks** | **4 piliers** | **~38h**

**A qui s'adresse cette serie** : etudiants en informatique (L3-M2), ingenieurs logiciel confrontes a des problemes d'optimisation, et candidats a des entretiens techniques. Les notebooks Python ne necessitent que Python 3.10+ avec `ortools` et `deap`. Les side tracks C# (edge detection, portefeuille) requierent .NET 9.0 + dotnet-interactive. Aucun prerequis en algorithmique avancee : les concepts sont introduits depuis les espaces d'etats.

## Pourquoi cette serie

La recherche et l'optimisation sont au coeur de l'informatique : tout probleme, du plus simple jeu de plateau a la planification logistique industrielle, se reduit a explorer un espace de solutions. Cette serie couvre **l'integralite du spectre algorithmique** — de la recherche aveugle (BFS) a l'hybridation LLM+CSP — en construisant une comprehension progressive des compromis fondamentaux.

Cette serie repose sur une **double approche**, delibement juxtaposee :

- **Exploration systematique** (recherche classique) : BFS, DFS, A*, Minimax — des algorithmes qui garantissent de trouver une solution optimale si elle existe, mais dont le cout peut etre exponentiel. C'est le domaine des espaces d'etats, des heuristiques admissibles, de la complétude.
- **Reduction de l'espace** (programmation par contraintes) : au lieu d'explorer betement, on elague les domaines impossibles par propagation (AC-3, Forward Checking, CP-SAT). C'est un changement de paradigme : on ne cherche plus, on contraint. Avantage : resolution de problemes industriels (ordonnancement, emploi du temps) en quelques millisecondes. Limite : la modelisation est un art.

Avoir les deux approches permet de comprendre **quand explorer, quand contraindre, et quand les combiner** — une competence cruciale pour tout ingenieur confronte a des problemes combinatoires.

Au-dela de la methodologie, cette serie couvre des **applications reelles** adaptees de projets etudiants : planification d'infirmiers (CHU), ordonnancement d'atelier (industrie), optimisation de portefeuille (finance), TSP/VRP (logistique), demineur (CSP + probabilites), Picross (couverture exacte). Chaque application est une brique construite sur les concepts precedents.

## Qu'est-ce que la recherche en IA ?

| Aspect | Exploration systematique | Programmation par contraintes | Metaheuristiques |
|--------|--------------------------|-------------------------------|-----------------|
| **Philosophie** | Enumerer methodiquement | Reduire les domaines impossibles | S'inspirer de la nature |
| **Garantie** | Solution optimale (si temps) | Solution optimale (si modelisable) | Aucune garantie |
| **Modelisation** | Espace d'etats (S, A, T, G) | Variables, domaines, contraintes | Fonction objectif, voisinage |
| **Complexite** | Exponentielle (mais heuristiques) | Exponentielle (mais propagation) | Polynomiale par iteration |
| **Quand l'utiliser** | Problemes bien definis, heuristique connue | Contraintes claires, domaine discret | Grands espaces, approximation acceptable |

## Objectifs d'apprentissage

A l'issue de cette serie, vous serez capable de :

1. **Formaliser** un probleme reel en espace d'etats (S, s0, A, T, G) et choisir l'algorithme de recherche adapte
2. **Comparer** recherche systematique (A*), contraintes (CSP) et metaheuristiques (GA, SA) sur un meme probleme
3. **Modeliser** un probleme industriel en CSP (ordonnancement, routing, emploi du temps) avec OR-Tools CP-SAT
4. **Evaluer** les compromis garantie vs performance vs generalisation pour choisir une strategie algorithmique
5. **Combiner** approches complementaires (CP+SAT, LLM+CSP, MCTS+DQN) pour des problemes complexes

## Parcours d'apprentissage

### Phase 1 : Fondements de la recherche (Part 1, notebooks 1-7, ~7h)

Le parcours commence par Search-1 (StateSpace) qui formalise les problèmes sous forme (S, s0, A, T, G) et Search-2 (Uninformed) qui couvre BFS, DFS, UCS et IDDFS. Search-3 (Informed) introduit les heuristiques et A*, le cœur de la recherche guidée. Search-4 (LocalSearch) pivote vers l'optimisation locale (Hill Climbing, Simulated Annealing, Tabu Search), et Search-5 (GeneticAlgorithms) généralise avec les algorithmes évolutionnaires. Search-6 (AdversarialSearch) explore la recherche dans les jeux (Minimax, Alpha-Beta), et Search-7 (MCTS) va jusqu'à Monte Carlo Tree Search et les approches AlphaGo. À l'issue de cette phase, vous maîtrisez les trois grands paradigmes : exploration systématique, optimisation locale, et recherche dans les jeux.

### Phase 2 : Programmation par contraintes (Part 2, CSP 1-6, ~6h)

La Phase 2 change de paradigme : au lieu d'explorer un espace, on le réduit. CSP-1 (Fundamentals) introduit le modèle (X, D, C) et le backtracking. CSP-2 (Consistency) couvre la propagation de contraintes (AC-3, Forward Checking, MAC). CSP-3 à CSP-6 montent en complexité : contraintes globales (AllDifferent, Cumulative), ordonnancement (Job-Shop, RCPSP), optimisation (Bin Packing, Knapsack), et hybridation (LCG, CP+SAT, CP+ML, LLM+CSP). Cette phase présuppose les bases de la Phase 1 (formalisation, backtracking = DFS) et constitue le cœur pratique de la série.

### Phase 3 : Applications et frontieres (Applications + notebooks avances, ~18h)

Les 20 notebooks d'applications illustrent chaque concept sur des cas réels : planification d'infirmiers (CSP-4), ordonnancement d'atelier (CSP-4), optimisation de portefeuille (métaheuristiques), TSP et VRP (routing), démineur et Wordle (CSP + théorie de l'information), Picross (couverture exacte). Les notebooks avancés de la Part 1 (programmation linéaire Search-9, automates symboliques Search-10, métaheuristiques Search-11) et de la Part 2 (contraintes souples CSP-7, temporelles CSP-8, distribuées CSP-9) complètent le panorama. L'ensemble est enrichi par des ponts vers les autres séries : Sudoku (DLX, automates), SymbolicAI (Z3, planification), GameTheory (Minimax, MCTS), et RL (MCTS + DQN).

## Vue d'ensemble

| Partie | Notebooks | Duree |
| -------- | --------- | ----- |
| Partie 1: Search Fondamental | 11 | ~12h30 |
| Partie 2: Programmation par Contraintes | 9 | ~9h |
| Applications | 20 | ~13h20 |
| Heritage (racine) | 5 | ~3h |
| **Total** | **45** | **~38h** |

| Statistique | Valeur |
|-------------|--------|
| Langages | Python (principal), C# (side tracks) |
| Niveau | Debutant a avance |

## Ce que chaque notebook apporte

Chaque notebook introduit un concept ou algorithme specifique. Le tableau ci-dessous resume en une ligne l'apport pedagogique de chacun.

### Partie 1 : Search Fondamental

| # | Notebook | Apport pedagogique |
|---|----------|-------------------|
| 1 | StateSpace | Formaliser un probleme en espace d'etats (S, s0, A, T, G) |
| 2 | Uninformed | BFS vs DFS : comment l'ordre d'exploration change la complexite |
| 3 | Informed | Heuristiques admissibles et A* : guider la recherche vers la solution |
| 4 | LocalSearch | Abandonner la garantie pour l'efficacite : paysages de fitness et optima locaux |
| 5 | GeneticAlgorithms | Populations, crossover, mutation : l'evolution comme metaheuristique |
| 6 | AdversarialSearch | Minimax, Alpha-Beta : chercher dans les jeux a deux joueurs |
| 7 | MCTS-And-Beyond | Monte Carlo Tree Search et la revolution AlphaGo (MCTS + DQN) |
| 8 | DancingLinks | Couverture exacte de Knuth : une structure de donnees transforme un algorithme |
| 9 | LinearProgramming | Programmation lineaire (PuLP) : relaxer les contraintes entieres |
| 10 | SymbolicAutomata | Automates finis + Z3 : raisonner sur des alphabets infinis |
| 11 | Metaheuristiques | PSO, ABC, BRO avec MEALPy : comparer 160+ algorithmes |

### Partie 2 : Programmation par Contraintes

| # | Notebook | Apport pedagogique |
|---|----------|-------------------|
| 1 | CSP Fundamentals | Modele (X, D, C) : declarer le probleme plutot que l'algorithme |
| 2 | CSP Consistency | AC-3, Forward Checking : reduire l'espace par propagation avant la recherche |
| 3 | CSP Advanced | Contraintes globales (AllDifferent, Cumulative, Circuit) |
| 4 | CSP Scheduling | Job-Shop, RCPSP, Nurse : l'ordonnancement industriel par contraintes |
| 5 | CSP Optimization | Bin Packing, Knapsack, Portfolio : optimiser sous contraintes |
| 6 | CSP Hybridization | LCG, CP+SAT, CP+ML, LLM+CSP : combiner les paradigmes |
| 7 | CSP Soft | Contraintes souples, Fuzzy CSP : quand toutes les contraintes ne sont pas egales |
| 8 | CSP Temporal | Allen's Interval Algebra, STP : raisonner sur le temps |
| 9 | CSP Distributed | ABT, AWC : resoudre des CSP repartis entre agents |

### Applications

| # | Notebook | Apport pedagogique |
|---|----------|-------------------|
| App-1 | NQueens | Le benchmark classique CSP : backtracking vs min-conflicts vs CP-SAT |
| App-2 | GraphColoring | Coloration de cartes : DSATUR vs CP-SAT, departements francais |
| App-3 | NurseScheduling | Planning infirmiers : contraintes hard/soft, modele CP-SAT |
| App-4 | JobShopScheduling | Ordonnancement industriel : IntervalVar, NoOverlap, makespan |
| App-5 | Timetabling | Emploi du temps : MiniZinc + CP-SAT, une modelisation declarative |
| App-6 | Minesweeper | Demineur : propagation CSP + probabilites + hybridation LLM |
| App-7 | Wordle | Solveur Wordle : filtrage CSP + theorie de l'information (entropy) |
| App-8 | MiniZinc | Modelisation declarative : syntaxe MiniZinc, contraintes globales |
| App-9 | EdgeDetection | Detection de bords par GA : PyGAD, filtres de convolution |
| App-10 | Portfolio | Frontiere de Pareto : optimisation multi-objectif de portefeuille |
| App-11 | Picross | Nonogrammes : speedup 27Mx CP-SAT vs naive |
| App-12 | ConnectFour | Puissance 4 : 8 algorithmes IA (Minimax, MCTS, DQN-RL) |
| App-13 | TSP | Voyageur de commerce : SA, GA, ACO, OR-Tools routing |
| App-14 | ConnectFour-Adversarial | Benchmark adversarial : Minimax vs Alpha-Beta vs MCTS |
| App-15 | SportsScheduling | Calendrier sportif : contraintes TV, equite, deplacements |
| App-16 | Crossword | Mots croises : backtracking, OR-Tools, generation |
| App-17 | VRP-Logistics | Vehicle Routing : SA, GA, ACO, CP-SAT |
| App-18 | HyperparameterTuning | Optimisation bayesienne de hyperparams : Optuna vs GA vs PSO |

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

Problemes du monde reel adaptes de projets etudiants.

### Applications Search (`Applications/Search/`)

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-12-ConnectFour](Applications/Search/App-12-ConnectFour.ipynb) | ~50 min | Puissance 4 : 8 algorithmes IA (Minimax, MCTS, DQN-RL) | Projet etudiant |
| 2 | [App-14-ConnectFour-Adversarial](Applications/Search/App-14-ConnectFour-Adversarial.ipynb) | ~45 min | Benchmark adversarial : Minimax, Alpha-Beta, MCTS | Projet etudiant |

### Applications CSP (`Applications/CSP/`)

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-1-NQueens](Applications/CSP/App-1-NQueens.ipynb) | ~30 min | Benchmark classique CSP : backtracking, min-conflicts, OR-Tools | Classique |
| 2 | [App-2-GraphColoring](Applications/CSP/App-2-GraphColoring.ipynb) | ~45 min | Coloration de cartes : Greedy, DSATUR, CP-SAT, departements francais | Projet etudiant |
| 3 | [App-3-NurseScheduling](Applications/CSP/App-3-NurseScheduling.ipynb) | ~60 min | Planning infirmiers : contraintes hard/soft, OR-Tools CP-SAT | Projet etudiant |
| 4 | [App-4-JobShopScheduling](Applications/CSP/App-4-JobShopScheduling.ipynb) | ~60 min | Ordonnancement industriel : intervalles, precedences, makespan | Projet etudiant |
| 5 | [App-5-Timetabling](Applications/CSP/App-5-Timetabling.ipynb) | ~50 min | Emploi du temps universitaire : MiniZinc + OR-Tools | Projet etudiant |
| 6 | [App-6-Minesweeper](Applications/CSP/App-6-Minesweeper.ipynb) | ~50 min | Demineur CSP : propagation, probabilites, hybride CSP+LLM | Projet etudiant |
| 7 | [App-7-Wordle](Applications/CSP/App-7-Wordle.ipynb) | ~45 min | Solveur Wordle : filtrage CSP + theorie de l'information | Projet etudiant |
| 8 | [App-8-MiniZinc](Applications/CSP/App-8-MiniZinc.ipynb) | ~50 min | Modelisation declarative : syntaxe MiniZinc, contraintes globales | Nouveau |
| 9 | [App-11-Picross](Applications/CSP/App-11-Picross.ipynb) | ~40 min | Nonogrammes : speedup 27Mx CP-SAT vs naive | Projet etudiant |
| 10 | [App-15-SportsScheduling](Applications/CSP/App-15-SportsScheduling.ipynb) | ~55 min | Calendrier sportif : contraintes TV, equite, deplacements | Projet etudiant |
| 11 | [App-16-Crossword-CSP](Applications/CSP/App-16-Crossword-CSP.ipynb) | ~45 min | Mots croises : backtracking, OR-Tools, generation | Projet etudiant |

### Applications Hybrides / Metaheuristiques (`Applications/Hybrid/`)

| # | Notebook | Duree | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [App-9-EdgeDetection](Applications/Hybrid/App-9-EdgeDetection.ipynb) | ~40 min | Detection de bords par GA : PyGAD, filtres de convolution | Existant (refonte) |
| 2 | [App-9b-EdgeDetection-CSharp](Applications/Hybrid/App-9b-EdgeDetection-CSharp.ipynb) | ~35 min | Side track C# : GeneticSharp pour detection de bords | Existant |
| 3 | [App-10-Portfolio](Applications/Hybrid/App-10-Portfolio.ipynb) | ~40 min | Optimisation de portefeuille : frontiere de Pareto, multi-objectif | Existant (refonte) |
| 4 | [App-10b-Portfolio-CSharp](Applications/Hybrid/App-10b-Portfolio-CSharp.ipynb) | ~30 min | Side track C# : GeneticSharp pour portefeuille | Existant |
| 5 | [App-13-TSP-Metaheuristics](Applications/Hybrid/App-13-TSP-Metaheuristics.ipynb) | ~50 min | TSP : SA, GA, ACO, OR-Tools routing | Classique |
| 6 | [App-17-VRP-Logistics](Applications/Hybrid/App-17-VRP-Logistics.ipynb) | ~60 min | Vehicle Routing : SA, GA, ACO, CP-SAT | Projet etudiant |
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
CSP-3  Advanced (OR-Tools) ───> Z3/01_Linq2Z3_Intro (SMT solving)
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

Les applications sont adaptees de projets etudiants. Les references specifics sont indiquees dans chaque notebook d'application.

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

## Progression recommandee

> Le parcours detaille avec prerequis et enchainements logiques est decrit dans la section [Parcours d'apprentissage](#parcours-dapprentissage) ci-dessus.

---

## Cross-series Bridges

| Serie | Lien | Connection |
|-------|------|-------------|
| [Sudoku](../Sudoku/README.md) | Resolution de puzzles | Les solveurs Sudoku (DLX, automates symboliques, CSP) sont des applications directes des techniques de cette serie |
| [SymbolicAI](../SymbolicAI/README.md) | IA symbolique | Z3 (SMT solving), planification PDDL et logique formelle prolongent les CSP vers la verification formelle |
| [GameTheory](../GameTheory/README.md) | Theorie des jeux | Minimax et MCTS (Search-6/7) sont aussi les algorithmes fondamentaux de la serie GameTheory |
| [Probas](../Probas/README.md) | Programmation probabiliste | Les approches probabilistes (MCTS, simulated annealing) partagent les memes fondements que les modeles probabilistes de la serie Probas |
| [RL](../RL/README.md) | Apprentissage par renforcement | MCTS (Search-7) et l'optimisation d'hyperparametres (App-18) relient la recherche au RL |
| [ML](../ML/README.md) | Machine Learning | L'optimisation bayesienne d'hyperparametres (App-18) applique les metaheuristiques de cette serie au ML |
| [GenAI](../GenAI/README.md) | IA generative | Les LLMs peuvent etre utilises comme heuristiques pour la resolution CSP (CSP-6 Hybridization) |
| Lecture transversale | [La mer qui monte](../../docs/grothendieckian-lens.md) | Grille de lecture grothendieckienne du depot : changement de representation, certification A/B/C |

## FAQ / Troubleshooting

### OR-Tools ne s'installe pas

OR-Tools necessite une version Python compatible. Sur Windows :
- Verifiez votre version Python : `python --version` (3.10-3.12 recommande)
- Installez avec : `pip install ortools` (les wheels precompiles sont disponibles pour la plupart des plateformes)
- Si echec : essayez `conda install -c conda-forge ortools-python`

### MiniZinc ne trouve pas son solveur

Le notebook App-8 utilise MiniZinc qui requiert l'installation de l'IDE :
- Telechargez depuis [minizinc.org](https://www.minizinc.org/software.html)
- Le solveur Gecode est inclus par defaut
- Verifiez : `minizinc --version` dans un terminal

### Les notebooks C# (.NET Interactive) ne s'executent pas

- Verifiez que .NET SDK 9.0+ est installe : `dotnet --version`
- Installez le kernel : `dotnet tool install -g Microsoft.dotnet-interactive && dotnet interactive jupyter install`
- Verifiez : `jupyter kernelspec list` doit afficher `.net-csharp`
- Les notebooks C# (App-9b, App-10b) utilisent GeneticSharp et SkiaSharp, installes automatiquement via `#r` dans les cellules

### DEAP ou PyGAD provoquent des erreurs d'import

- DEAP : `pip install deap` — compatible Python 3.8+
- PyGAD : `pip install pygad` — requiert numpy. Si conflit : `pip install --upgrade numpy pygad`
- MEALPy (Search-11) : `pip install mealpy` — dependances nombreuses, preferez un env dedie

### Les solveurs CP-SAT sont lents sur mon probleme

- Verifiez que vous utilisez `model.parameters.max_time_in_seconds` pour limiter le temps
- Les contraintes globales (AllDifferent, Cumulative) sont beaucoup plus efficaces que des contraintes binaires equivalentes
- Activez la parallelisation : `solver.parameters.num_workers = 8`
- Consultez le [CP-SAT Primer](https://github.com/google/or-tools/blob/stable/ortools/sat/docs/CP-SAT_Primer.md) pour les bonnes pratiques

### Comment choisir entre A*, CSP et metaheuristiques ?

- **Espace d'etats petit, solution optimale requise** : A* avec heuristique admissible
- **Contraintes complexes, domaine discret** : CP-SAT (OR-Tools)
- **Grands espaces, approximation acceptable** : Metaheuristiques (GA, SA, PSO)
- **Probleme de jeux, deux adversaires** : Minimax / Alpha-Beta / MCTS
- **Probleme NP-difficile, temps limite** : LNS (Large Neighborhood Search) dans CP-SAT

## Quel parcours choisir ?

### Si vous decouvrez la recherche en IA

Commencez par **Search-1 (StateSpace)** et **Search-2 (Uninformed)** pour comprendre la formalisation des problemes et les algorithmes fondamentaux (BFS, DFS). Puis **Search-3 (Informed)** pour decouvrir A* et les heuristiques. C'est le socle commun a toute la serie.

### Si vous venez de la programmation par contraintes

Commencez par **CSP-1 (Fundamentals)** et **CSP-2 (Consistency)** si vous connaissez deja les espaces d'etats. Puis montez en complexite avec **CSP-3-6** et les applications industrielles (**App-3 NurseScheduling**, **App-4 JobShop**).

### Si vous preparez un entretien technique

Concentrez-vous sur **Search-1 a Search-3** (espaces d'etats, BFS/DFS, A*), **Search-6 (AdversarialSearch)** (Minimax) et **CSP-1-2** (backtracking, propagation). Ce sont les algorithmes les plus frequemment demandes.

### Si vous voulez resoudre un probleme industriel

Allez directement aux applications qui correspondent a votre domaine : **App-3/App-4** (ordonnancement), **App-13/App-17** (routing/logistique), **App-5** (emploi du temps), ou **App-10** (optimisation portefeuille). Chaque application est autonome avec les prerequis indiques.

---

## Licence

Voir la licence du repository principal.

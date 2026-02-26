# Sudoku - Resolution par Differentes Approches Algorithmiques

Cette serie de **31 notebooks** explore differentes techniques de resolution de Sudoku, des algorithmes classiques aux approches symboliques, probabilistes et neuronales. Les notebooks sont disponibles en **approche miroir C#/Python** pour permettre aux etudiants de choisir leur langage.

## Pourquoi etudier le Sudoku en IA ?

Le Sudoku est bien plus qu'un simple jeu de grilles : c'est un **paradigme fondamental** de l'informatique et de l'intelligence artificielle. Son etude revele des concepts essentiels qui s'appliquent a de nombreux problemes reels.

### Contexte historique et theorie de la complexite

Le Sudoku generalise (n x n) est un probleme **NP-complet**, ce qui signifie qu'il n'existe pas d'algorithme polynomial connu pour le resoudre dans tous les cas. Cette proprietee le place dans la meme classe de complexite que le probleme du voyageur de commerce ou la satisfaction de contraintes boolennes (SAT).

Cette caracteristique fait du Sudoku un excellent banc d'essai pour comparer differentes strategies algorithmiques : comment des approches tres differentes (enumeration, metaheuristiques, contraintes, apprentissage) se comportent-elles face a un meme probleme computationnel ?

### Concepts fondamentaux enseignes

| Concept | Illustration dans le Sudoku | Application reelle |
|---------|----------------------------|-------------------|
| **Recherche dans un espace d'etats** | Chaque grille est un etat, les mouvements legaux definissent les transitions | Planification robotique, jeux |
| **Propagation de contraintes** | Eliminer les candidats impossibles reduit l'espace de recherche | Calibration de capteurs, ordonnancement |
| **Heuristiques de choix** | MRV (Minimum Remaining Values) guide vers les decisions les plus contraignantes | Diagnostic medical, detection de fraudes |
| **Metaheuristiques d'optimisation** | Recuit simule, algorithmes genetiques pour explorer intelligemment | Logistique, conception de circuits |
| **Programmation par contraintes** | Declarer les regles plutot que l'algorithme de resolution | Emploi du temps, configuration produit |
| **Satisfiabilite modulaire (SMT)** | Combinaison de theorie des ensembles et d'arithmetique | Verification de programmes, preuve de theoremes |
| **Apprentissage automatique** | Entrainement sur des millions de grilles pour apprendre des patterns | Vision par ordinateur, traduction |

### Pourquoi ce parcours pedagogique ?

La resolution du Sudoku permet de comprendre **l'evolution historique de l'IA** :

1. **IA symbolique classique** (annnees 1960-1990) : backtracking, propagation, CSP
2. **Metaheuristiques** (annnees 1980-2000) : algorithmes inspires de la nature
3. **Solveurs SMT/CP modernes** (annnees 2000-present) : outils industriels puissants
4. **IA connexionniste** (annnees 2010-present) : reseaux de neurones, LLM

Chaque approche reflete une philosophie differente de la resolution de problemes et offre des compromis uniques entre garantie de solution, performance et generalisabilite.

---

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 31 (16 C#, 15 Python) |
| Duree estimee | ~8h |
| Niveau | Debutant a avance |
| Langages | C# (.NET Interactive), Python |

---

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
    └── PSO

Niveau 4 : Programmation par Contraintes (CSP)
    ├── AIMA CSP (reference academique)
    ├── Propagation de Norvig (MRV + Forward Checking)
    ├── Strategies Humaines (13 techniques d'infenrence)
    ├── Graph Coloring (formulation graphe du CSP)
    ├── OR-Tools CP-SAT (bibliotheque industrielle)
    └── Choco Solver (autre bibliotheque CP)

Niveau 5 : IA Symbolique (SMT, Automates)
    ├── Z3 SMT Solver
    ├── Automates Symboliques + Z3
    └── BDD/MDD (diagrammes de decision)

Niveau 6 : IA Moderne / Data-Driven
    ├── Infer.NET (probabiliste)
    ├── Reseau de Neurones (CNN)
    └── LLM Solver

Niveau 7 : Synthese
    └── Benchmark Comparatif
```

### Ce que chaque niveau enseigne

**Niveau 1 - Recherche Exhaustive** : Comprendre l'espace de recherche. Le backtracking est l'algorithme fondamental qui enumere systematiquement toutes les possibilites. Il garantit de trouver une solution si elle existe, mais peut etre exponentiel dans le pire cas.

**Niveau 2 - Optimisation Structurelle** : Dancing Links (Knuth, 2000) montre comment une representation de donnees intelligente (listes doublement chainees) peut transformer radicalement les performances. Ce n'est pas un nouvel algorithme, mais une implementation optimisee du backtracking.

**Niveau 3 - Metaheuristiques** : Abandonner la garantie pour l'efficacite pratique. Ces algorithmes s'inspirent de la nature (evolution, physique, essaimage) pour explorer intelligemment l'espace de recherche sans garantir l'optimalite.

**Niveau 4 - Programmation par Contraintes** : Declarer le "quoi" plutot que le "comment". On specifie les contraintes (ligne, colonne, bloc uniques) et le solveur trouve la solution. Approche declarative et industrielle.

**Niveau 5 - IA Symbolique Avancee** : Utiliser des outils formels (SMT, BDD) qui combinent raisonnement logique et efficacite computationnelle. Ces techniques sont utilisees en verification de logiciels et en preuve de theoremes.

**Niveau 6 - IA Data-Driven** : Apprendre a resoudre plutot que programmer la resolution. Les reseaux de neurones apprennent des patterns dans les donnees, tandis que les LLM utilisent des connaissances linguistiques.

---

## Comparaison des Approches : Quand Utiliser Quoi ?

### Approches exhaustives vs heuristiques

| Critere | Approches Exhaustives | Approches Heuristiques |
|---------|----------------------|------------------------|
| **Garantie de solution** | Oui (si solution existe) | Non (peut echouer) |
| **Complexite pire cas** | Exponentielle | Souvent polynomiale |
| **Performance pratique** | Variable selon instance | Plus previsible |
| **Problemes adressables** | Tous | Grands espaces, approximations acceptables |

### Arbitrages fondamentaux

**Vitesse vs Garantie** : Un algorithme genetique peut trouver une solution en quelques millisecondes, mais ne garantit pas de la trouver. OR-Tools prendra peut-etre plus de temps, mais trouvera toujours la solution optimale.

**Simplicite vs Efficacite** : Le backtracking s'implemente en 20 lignes de code. Dancing Links requiert une comprehension approfondie des structures de donnees mais est 10x plus rapide.

**Declaratif vs Imperatif** : En programmation par contraintes, on decrit les regles du Sudoku et le solveur fait le reste. En backtracking, on programme explicitement l'exploration.

### Applications reelles par technique

| Technique | Applications industrielles |
|-----------|---------------------------|
| **Backtracking** | Analysis syntaxique, resolution de puzzles, generation de combinaisons |
| **Dancing Links** | Problemes de couverture exacte, planification |
| **Algorithmes genetiques** | Conception de circuits, optimisation de portefeuilles, design de molecules |
| **Recuit simule** | Routage de circuits, ordonnancement de production |
| **PSO** | Optimisation de reseaux, calibration de modeles |
| **OR-Tools/CP** | Emplois du temps, logistique, allocation de ressources |
| **Z3/SMT** | Verification de programmes, analyse de securite, preuve de theoremes |
| **BDD/MDD** | Verification de circuits, compilation de requetes |
| **Reseaux de neurones** | Reconnaissance d'images, traduction, jeux |

### Quand choisir quelle approche ?

- **Probleme petit, garantie requise** : Backtracking, Dancing Links
- **Probleme NP-difficile, solution rapide** : Metaheuristiques
- **Contraintes complexes, besoin de flexibilite** : Programmation par contraintes (OR-Tools, Choco)
- **Raisonnement formel requis** : Z3, SMT
- **Donnees abondantes, generalisation souhaitee** : Reseau de neurones
- **Pas d'algorithme connu, intuition humaine** : LLM

---

## Parcours d'Apprentissage Recommandes

### Parcours Debutant : Comprendre les Fondamentaux

**Objectif** : Maitriser la recherche exhaustive et comprendre pourquoi elle est insuffisante.

**Notebooks recommandes** :
1. `Sudoku-0-Environment-Csharp` ou comprendre la structure des donnees
2. `Sudoku-1-Backtracking-Csharp` (ou Python) : Premier algorithme de resolution
3. `Sudoku-7-Norvig-Csharp` : Voir comment la propagation accelere drastiquement

**Pourquoi cet ordre ?**
- Le notebook 0 etablit le vocabulaire et les structures de base
- Le notebook 1 montre l'approche naive et ses limitations
- Le notebook 7 demontre qu'une simple optimisation (propagation) peut donner des gains de 100x

**Cles de comprehension** :
- L'espace de recherche du Sudoku est immense : 9^81 configurations possibles
- Le backtracking explore cet espace intelligemment mais peut encore etre lent
- La propagation de contraintes reduit l'espace avant meme de chercher

### Parcours Intermediaire : Explorer les Paradigmes

**Objectif** : Comprendre que differentes philosophies de resolution existent et ont chacune leurs forces.

**Notebooks recommandes** :
1. `Sudoku-3-Genetic-Csharp` (ou Python) : Decouvrir les metaheuristiques
2. `Sudoku-9-GraphColoring-Csharp` (ou Python) : Voir le Sudoku comme un probleme de graphe
3. `Sudoku-10-ORTools-Csharp` (ou Python) : Utiliser un outil industriel

**Pourquoi cet ordre ?**
- Le notebook 3 montre qu'on peut "abandonner" la garantie pour la vitesse
- Le notebook 9 change completement de perspective (theorie des graphes)
- Le notebook 10 introduit l'approche declarative moderne

**Cles de comprehension** :
- Les metaheuristiques sont puissantes mais non deterministes
- Reformuler un probleme peut reveler des algorithmes optimaux
- Les outils industriels encapsulent des decennies de recherche

### Parcours Avance : Maitriser l'IA Symbolique et Data-Driven

**Objectif** : Utiliser les outils de pointe de l'IA moderne.

**Notebooks recommandes** :
1. `Sudoku-12-Z3-Csharp` (ou Python) : Satisfiabilite modulaire
2. `Sudoku-16-NeuralNetwork-Python` : Apprentissage profond
3. `Sudoku-17-LLM-Python` : Grands modeles de langage
4. `Sudoku-18-Comparison-Python` : Benchmark comparatif final

**Pourquoi cet ordre ?**
- Le notebook 12 montre l'apogee de l'IA symbolique (outils de verification formelle)
- Le notebook 16 introduit l'apprentissage : le modele apprend a resoudre
- Le notebook 17 teste les limites des LLM sur un probleme logique pur
- Le notebook 18 synthetise toutes les approches

**Cles de comprehension** :
- Z3 represente des decennies d'optimisation en raisonnement automatique
- Les reseaux de neurones peuvent apprendre des heuristiques mais ne garantissent rien
- Les LLM sont surprenants : ils peuvent resoudre des Sudokus sans algorithme explicite
- Le choix de l'approche depend du contexte : garantie vs vitesse vs generalisation

---

## Points Cles a Retenir par Niveau

### Niveau 1-2 : Recherche Exhaustive

**A retenir** :
- Le backtracking est l'algorithme de base, comprendre sa recursion est fondamental
- L'ordre d'exploration (heuristique de choix) impacte drastiquement les performances
- Dancing Links montre que les structures de donnees peuvent transformer un algorithme

**Pieges courants** :
- Confondre complexite moyenne et pire cas
- Negliger l'importance de l'heuristique de choix (MRV)
- Sous-estimer l'impact de la propagation de contraintes

### Niveau 3 : Metaheuristiques

**A retenir** :
- Ces algorithmes s'inspirent de processus naturels
- Ils ne garantissent pas la solution mais sont souvent tres efficaces
- Le parametrage (taux de mutation, temperature, etc.) est crucial et delicat

**Pieges courants** :
- Attendre une garantie de solution
- Mal regler les hyperparametres
- Utiliser une metaheuristique quand un algorithme exact suffirait

### Niveau 4 : Programmation par Contraintes

**A retenir** :
- On declare les contraintes, le solveur fait le reste
- OR-Tools et Choco sont des outils industriels tres optimises
- La propagation de contraintes est la cle de l'efficacite

**Pieges courants** :
- Sur-contraindre (pas de solution) ou sous-contraindre (trop de solutions)
- Ignorer les heuristiques de branchement du solveur
- Ne pas profiter des capacites de parallelisation

### Niveau 5 : IA Symbolique

**A retenir** :
- Z3 combine theorie des ensembles, arithmetique et logique
- Les BDD representent compactement des ensembles de solutions
- Ces outils sont utilises en verification de logiciels critiques

**Pieges courants** :
- Ecrire des contraintes inefficaces pour le solveur
- Ignorer les theories integrees (arithmetique lineaire vs non-lineaire)
- Sous-estimer la puissance de la resolution SAT/SMT moderne

### Niveau 6 : IA Data-Driven

**A retenir** :
- Les reseaux de neurones apprennent des patterns mais sans garantie
- Les LLM utilisent des connaissances implicites du web
- Ces approches sont complementaires, non concurrentes, des methodes symboliques

**Pieges courants** :
- Attendre 100% de succes des modeles appris
- Ignorer le besoin de donnees d'entrainement massives
- Confondre performance sur donnees connues vs inconnues

---

## Structure des Notebooks

| # | Sujet | C# | Python | Technologie Python |
|---|-------|----|----|-------------------|
| 0 | Environment | Oui | - | - |
| 1 | Backtracking | Oui | Oui | Backtracking + MRV |
| 2 | Dancing Links | Oui | Oui | Algorithm X from scratch |
| 3 | Genetic | Oui | Oui | PyGAD |
| 4 | Simulated Annealing | Oui | Oui | `simanneal` |
| 5 | PSO | Oui | Oui | `mealpy` |
| 6 | AIMA CSP | Oui | Oui | Port Russell & Norvig |
| 7 | Norvig | Oui | Oui | Original Norvig |
| 8 | Human Strategies | Oui | Oui | Port C# vers Python |
| 9 | Graph Coloring | Oui | Oui | **networkx** + `nx.sudoku_graph()` |
| 10 | OR-Tools | Oui | Oui | **ortools** CP-SAT |
| 11 | Choco | Oui | Oui | **JPype** + Choco JAR |
| 12 | Z3 | Oui | Oui | **z3-solver** |
| 13 | Symbolic Automata | Oui | - | (C# uniquement) |
| 14 | BDD | Oui | - | (C# uniquement) |
| 15 | Infer (Probabiliste) | Oui | Oui | **NumPyro** + JAX |
| 16 | Neural Network | - | Oui | **PyTorch** CNN |
| 17 | LLM | - | Oui | **Semantic Kernel** |
| 18 | Comparison | - | Oui | Benchmark comparatif |

**Legende** : Oui = disponible, - = non applicable

## Notebooks avec Versions Miroir C#/Python

Les notebooks suivants sont disponibles dans les deux langages pour comparaison directe :

| # | Sujet | C# | Python | Interet pedagogique |
|---|-------|----|----|-------------------|
| 1 | Backtracking | [Sudoku-1-Backtracking-Csharp](Sudoku-1-Backtracking-Csharp.ipynb) | [Sudoku-1-Backtracking-Python](Sudoku-1-Backtracking-Python.ipynb) | Algorithme de base |
| 2 | Dancing Links | [Sudoku-2-DancingLinks-Csharp](Sudoku-2-DancingLinks-Csharp.ipynb) | [Sudoku-2-DancingLinks-Python](Sudoku-2-DancingLinks-Python.ipynb) | Couverture exacte |
| 3 | Genetic | [Sudoku-3-Genetic-Csharp](Sudoku-3-Genetic-Csharp.ipynb) | [Sudoku-3-Genetic-Python](Sudoku-3-Genetic-Python.ipynb) | GeneticSharp vs PyGAD |
| 9 | Graph Coloring | [Sudoku-9-GraphColoring-Csharp](Sudoku-9-GraphColoring-Csharp.ipynb) | [Sudoku-9-GraphColoring-Python](Sudoku-9-GraphColoring-Python.ipynb) | Theorie des graphes |
| 10 | OR-Tools | [Sudoku-10-ORTools-Csharp](Sudoku-10-ORTools-Csharp.ipynb) | [Sudoku-10-ORTools-Python](Sudoku-10-ORTools-Python.ipynb) | CP-SAT solveur |
| 12 | Z3 | [Sudoku-12-Z3-Csharp](Sudoku-12-Z3-Csharp.ipynb) | [Sudoku-12-Z3-Python](Sudoku-12-Z3-Python.ipynb) | SMT solveur |

## Algorithmes Couverts

| Algorithme | Type | Performance | Fiabilite | Notebook C# | Notebook Python |
|------------|------|-------------|-----------|-------------|-----------------|
| **Backtracking** | Recherche exhaustive | Rapide (Easy) | Garantie | 1 | 1 |
| **Dancing Links** | Couverture exacte | Optimal | Garantie | 2 | 2 |
| **Algorithme Genetique** | Metaheuristique | Variable | Non garanti | 3 | 3 |
| **Recuit Simule** | Recherche locale | Variable | Non garanti | 4 | 4 |
| **PSO** | Swarm Intelligence | Variable | Non garanti | 5 | 5 |
| **AIMA CSP** | Contraintes academique | Rapide | Garantie | 6 | 6 |
| **Norvig Propagation** | Propagation | Tres rapide | Garantie | 7 | 7 |
| **Strategies Humaines** | Deduction logique | Variable | Partielle | 8 | 8 |
| **Graph Coloring** | Theorie des graphes | Moyen | Garantie | 9 | 9 |
| **OR-Tools CP-SAT** | CP industrielle | Tres rapide | Garantie | 10 | 10 |
| **Choco Solver** | CP industrielle | Rapide | Garantie | 11 | 11 |
| **Z3 SMT** | Satisfiabilite | Rapide | Garantie | 12 | 12 |
| **Symbolic Automata** | Automates + SMT | Rapide | Garantie | 13 | - |
| **BDD/MDD** | Diagrammes decision | Moyen | Garantie | 14 | - |
| **Infer.NET/NumPyro** | Inference probabiliste | Experimental | Variable | 15 | 15 |
| **Reseau de Neurones** | Deep Learning | Rapide (inference) | Approx. | - | 16 |
| **LLM Solver** | LLM | Variable | ~10-30% | - | 17 |

## Progression Recommandee

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
    +---> Niveau 4 : Sudoku-6/7/8/9/10/11-Csharp (CSP)
    |
    +---> Niveau 5 : Sudoku-12/13/14-Csharp (Symbolique)
    |
    +---> Niveau 6 : Sudoku-15-Csharp (Infer.NET)
    |
    +---> Niveau 7 : Sudoku-18-Comparison-Python (Benchmark)
```

### Parcours Python (Complet)
```
Sudoku-0-Csharp (Environment - comprendre les structures)
    |
    +---> Niveau 1 : Sudoku-1-Backtracking-Python
    |
    +---> Niveau 2 : Sudoku-2-DancingLinks-Python
    |
    +---> Niveau 3 : Sudoku-3/4/5-Python (Metaheuristiques)
    |
    +---> Niveau 4 : Sudoku-6/7/8/9/10/11/12-Python (CSP + SMT)
    |
    +---> Niveau 6 : Sudoku-16/17-Python (NN + LLM)
    |
    +---> Niveau 7 : Sudoku-18-Comparison-Python
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

**Note sur les outputs** : Les notebooks C# (.NET Interactive) ne contiennent pas de outputs de cellule executees.

### Python

```bash
# Creer un environnement
python -m venv venv

# Installer les dependances
pip install numpy matplotlib ortools z3-solver pygad torch networkx mealpy simanneal jpype1 semantic-kernel
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
| LLM | Variable | Variable | ~10-30% succes | ~10-30% succes |
| Infer.NET | ~1s | ~5s | Variable | Variable |

## Sources des Projets Etudiants

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
├── Sudoku-0-Environment-Csharp.ipynb      # Classes de base C#
├── Sudoku-1-Backtracking-Csharp.ipynb     # Backtracking C#
├── Sudoku-1-Backtracking-Python.ipynb     # Backtracking Python
├── Sudoku-2-DancingLinks-Csharp.ipynb     # Dancing Links C#
├── Sudoku-2-DancingLinks-Python.ipynb     # Dancing Links Python
├── Sudoku-3-Genetic-Csharp.ipynb          # Algorithme genetique C#
├── Sudoku-3-Genetic-Python.ipynb          # Algorithme genetique Python
├── Sudoku-4-SimulatedAnnealing-Csharp.ipynb  # Recuit simule C#
├── Sudoku-4-SimulatedAnnealing-Python.ipynb  # Recuit simule Python
├── Sudoku-5-PSO-Csharp.ipynb              # PSO C#
├── Sudoku-5-PSO-Python.ipynb              # PSO Python
├── Sudoku-6-AIMA-CSP-Csharp.ipynb         # AIMA CSP C#
├── Sudoku-6-AIMA-CSP-Python.ipynb         # AIMA CSP Python
├── Sudoku-7-Norvig-Csharp.ipynb           # Propagation de Norvig C#
├── Sudoku-7-Norvig-Python.ipynb           # Propagation de Norvig Python
├── Sudoku-8-HumanStrategies-Csharp.ipynb  # Strategies humaines C#
├── Sudoku-8-HumanStrategies-Python.ipynb  # Strategies humaines Python
├── Sudoku-9-GraphColoring-Csharp.ipynb    # Graph Coloring C#
├── Sudoku-9-GraphColoring-Python.ipynb    # Graph Coloring Python
├── Sudoku-10-ORTools-Csharp.ipynb         # OR-Tools C#
├── Sudoku-10-ORTools-Python.ipynb         # OR-Tools Python
├── Sudoku-11-Choco-Csharp.ipynb           # Choco Solver C#
├── Sudoku-11-Choco-Python.ipynb           # Choco Solver Python
├── Sudoku-12-Z3-Csharp.ipynb              # Z3 SMT C#
├── Sudoku-12-Z3-Python.ipynb              # Z3 SMT Python
├── Sudoku-13-SymbolicAutomata-Csharp.ipynb # Automates symboliques C#
├── Sudoku-14-BDD-Csharp.ipynb             # BDD/MDD C#
├── Sudoku-15-Infer-Csharp.ipynb           # Infer.NET C#
├── Sudoku-15-Infer-Python.ipynb           # NumPyro Python
├── Sudoku-16-NeuralNetwork-Python.ipynb   # Reseau de neurones Python
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

### Bibliotheques
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

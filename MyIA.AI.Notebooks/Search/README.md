# Search - Algorithmes de Recherche et Optimisation

Cette serie de **5 notebooks** explore les algorithmes de recherche et d'optimisation, des methodes non informees aux metaheuristiques comme les algorithmes genetiques.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 5 (3 Python, 2 C#) |
| Cellules totales | 95 (MD: 50, Code: 45) |
| Duree estimee | ~1h10 |

## Structure

| # | Notebook | Kernel | Cellules | Duree | Contenu |
|---|----------|--------|----------|-------|---------|
| 1 | [CSPs_Intro](CSPs_Intro.ipynb) | Python | 24 | ~19 min | Programmation par contraintes, Backtracking, AC-3, N-Queens, Min-Conflicts |
| 2 | [Exploration_non_informee](Exploration_non_informée_et_informée_intro.ipynb) | Python | 24 | ~17 min | BFS, DFS, A*, Hill Climbing, Simulated Annealing |
| 3 | [GeneticSharp-EdgeDetection](GeneticSharp-EdgeDetection.ipynb) | C# | 18 | ~14 min | Detection de bords avec GeneticSharp |
| 4 | [Portfolio_Optimization](Portfolio_Optimization_GeneticSharp.ipynb) | C# | 11 | ~8 min | Optimisation de portefeuille financier |
| 5 | [PyGad-EdgeDetection](PyGad-EdgeDetection.ipynb) | Python | 18 | ~13 min | Detection de bords avec PyGAD |

## Contenu Detaille

### CSPs_Intro - Programmation par Contraintes

Introduction complete a la resolution de problemes de satisfaction de contraintes (CSP).

| Section | Contenu |
|---------|---------|
| Coloration de graphe | Exemple minimal, modelisation CSP |
| Backtracking | Principe, implementation de base |
| Heuristiques | MRV, Degree, LCV |
| Arc Consistency | Algorithme AC-3 |
| N-Queens | Application classique |
| Min-Conflicts | Recherche locale pour CSP |

### Exploration - Recherche Non Informee et Informee

Panorama des algorithmes de recherche dans un espace d'etats.

| Algorithme | Type | Completude | Optimalite |
|------------|------|------------|------------|
| **BFS** | Non informee | Oui | Oui (cout uniforme) |
| **DFS** | Non informee | Non | Non |
| **A*** | Informee | Oui | Oui (h admissible) |
| **Hill Climbing** | Locale | Non | Non |
| **Simulated Annealing** | Locale | Non | Non garanti |
| **Genetic Algorithm** | Metaheuristique | Non | Non garanti |

### GeneticSharp - Detection de Bords (C#)

Application des algorithmes genetiques a la detection de contours dans les images.

| Composant | Description |
|-----------|-------------|
| Chromosome | Filtre de convolution 3x3 |
| Fitness | Similarite avec filtre Sobel de reference |
| Selection | Tournament |
| Crossover | Uniform |
| Mutation | Flip genes |

### PyGad - Detection de Bords (Python)

Meme probleme que GeneticSharp mais avec PyGAD en Python.

| Parametre | Valeur |
|-----------|--------|
| Population | 50 individus |
| Generations | 100 |
| Mutation | 0.1 |
| Crossover | Single point |

## Prerequis

### Python

```bash
# Installer les dependances
pip install numpy matplotlib pygad scikit-image
```

### C# (.NET Interactive)

```bash
# Les packages NuGet sont installes dans les notebooks :
# - GeneticSharp
# - SkiaSharp (visualisation)
```

## Concepts Cles

| Concept | Description |
|---------|-------------|
| **CSP** | Constraint Satisfaction Problem - variables, domaines, contraintes |
| **Backtracking** | Exploration systematique avec retour arriere |
| **Arc Consistency** | Reduction des domaines par propagation |
| **Heuristique** | Fonction guidant la recherche (f = g + h pour A*) |
| **Metaheuristique** | Strategie de haut niveau pour l'optimisation |
| **Algorithme Genetique** | Evolution de population, selection, crossover, mutation |
| **Fitness** | Mesure de qualite d'une solution candidate |

## Applications

| Notebook | Application | Domaine |
|----------|-------------|---------|
| CSPs_Intro | Coloration de graphe, N-Queens | Combinatoire |
| Exploration | Planification d'itineraire | Navigation |
| EdgeDetection | Detection de contours | Vision par ordinateur |
| Portfolio | Allocation d'actifs | Finance |

## Ressources

### Programmation par Contraintes
- [Constraint Processing - Rina Dechter](https://www.cambridge.org/core/books/constraint-processing/4A96AFE2EC4BDC8C85FAE8A2A7508E60)
- [python-constraint](https://pypi.org/project/python-constraint/)

### Recherche et Optimisation
- [AIMA - Russell & Norvig](http://aima.cs.berkeley.edu/)
- [simpleai](https://simpleai.readthedocs.io/)

### Algorithmes Genetiques
- [GeneticSharp](https://github.com/giacomelli/GeneticSharp)
- [PyGAD Documentation](https://pygad.readthedocs.io/)

## Structure des Fichiers

```
Search/
├── CSPs_Intro.ipynb
├── Exploration_non_informée_et_informée_intro.ipynb
├── GeneticSharp-EdgeDetection.ipynb
├── Portfolio_Optimization_GeneticSharp.ipynb
├── PyGad-EdgeDetection.ipynb
├── resources/
│   └── images/                # Images pour detection de bords
└── README.md
```

## Licence

Voir la licence du repository principal.

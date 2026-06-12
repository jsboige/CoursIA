# Serie Z3 - Programmation Declarative avec Z3.Linq

**Navigation** : [Index SymbolicAI](../README.md) | [Index general](../../README.md)

## Serie en quelques mots

**5 notebooks** | **1 kernel** | **~4h de travail** | **Z3.Linq (.NET 9)**

**A qui s'adresse cette serie** : etudiants en IA, developpeurs C# souhaitant decouvrir la programmation par contraintes, et tout curieux voulant comprendre comment exprimer un probleme non pas comme un algorithme de resolution, mais comme un ensemble de contraintes que le solveur satisfait automatiquement. Aucun prerequis en logique formelle n'est suppose : les notebooks partent de theoremes lineaires simples pour monter progressivement vers les theories de tableaux et l'optimisation hierarchique.

## Presentation

**Z3** (Microsoft Research) est un solveur SMT (*Satisfiability Modulo Theories*) qui resout des systemes de contraintes sur des entiers, des reels, des booleens et des tableaux. **Z3.Linq** est un binding qui traduit des expressions LINQ C# en formules SMT, permettant de modeliser des problemes declarativement sans ecrire les appels Z3 bas niveau.

L'interet pedagogique : au lieu d'ecrire un algorithme de backtracking pour un Sudoku ou un planificateur de repas, on decrit les contraintes (une seule valeur par case, pas de doublon par ligne, apports nutritionnels requis) et le solveur trouve les solutions. Ce changement de paradigme — de l'imperatif au declaratif — est au coeur de cette serie.

### Declaratif vs Imperatif

| Aspect | Imperatif (classique) | Declaratif (Z3.Linq) |
|--------|----------------------|---------------------|
| **Approche** | Ecrire l'algorithme de resolution | Decrire les contraintes, laisser le solveur resoudre |
| **Complexite** | Backtracking, heuristiques, pruning | Syntaxe LINQ naturelle en C# |
| **Evolution** | Modifier l'algorithme pour chaque nouveau probleme | Ajouter des contraintes, le solveur s'adapte |
| **Verification** | Tester les solutions | Les solutions satisfont les contraintes par construction |
| **Limite** | Difficile a generaliser | Performance sur les tres grandes instances |

## Vue d'ensemble

| # | Notebook | Sujet | Duree | Statut |
|---|----------|-------|------|--------|
| 01 | [Linq2Z3 Intro](01_Linq2Z3_Intro.ipynb) | Theoremes lineaires, Missionnaires-Cannibales, optimisation | ~45 min | PRODUCTION |
| 02 | [Sudoku Theorem vs Array](02_Sudoku_Theorem_vs_Array.ipynb) | Sudoku explicite (81 proprietes) vs implicite (`List<int>` + lambdas/closures) | ~50 min | PRODUCTION |
| 03 | [Array Theory](03_Array_Theory.ipynb) | Z3 array theory : Select/Store, switching dynamique | ~45 min | BETA |
| 04 | [Nested Arrays 2D](04_Nested_Arrays_2D.ipynb) | Tableaux imbriques, grilles 2D, Sudoku 4x4, carre magique | ~40 min | BETA |
| 05 | [Meal Planner Hierarchical](05_Meal_Planner_Hierarchical.ipynb) | Planificateur de repas : data fusion LINQ + theoreme hierarchique | ~50 min | BETA |

### Fil pedagogique

1. **Notebook 01** pose les bases : le patron `Theorem<T>` de Z3.Linq, les theoremes lineaires, la recherche de plus court chemin, et le classique Missionnaires-Cannibales
2. **Notebook 02** compare deux approches du Sudoku : 81 proprietes explicites vs modelisation implicite via arrays et lambdas
3. **Notebook 03** plonge dans la theorie des tableaux Z3 (Select/Store), avec switching dynamique entre representations
4. **Notebook 04** generalise aux tableaux imbriques (2D) : grilles, carres magiques, Sudoku 4x4
5. **Notebook 05** integre tout : data fusion LINQ + theoreme hierarchique multi-niveaux pour un planificateur de repas realiste

## Prerequis

| Besoin | Detail |
|--------|--------|
| **.NET 9.0 SDK** | [Download](https://dotnet.microsoft.com/download/dotnet/9.0) |
| **.NET Interactive** | `dotnet tool install --global Microsoft.dotnet-interactive` |
| **Kernel Jupyter** | `.net-csharp` (installe automatiquement par .NET Interactive) |
| **Package NuGet** | `Z3.Linq` (charge automatiquement dans les notebooks via `#r nuget:...`) |

> Les notebooks sont autonomes : le restore NuGet et l'initialisation du contexte Z3 sont inclus dans les cellules de setup de chaque notebook.

## Objectifs d'apprentissage

A l'issue de cette serie, l'etudiant sera capable de :

1. **Modeliser** un probleme de satisfaction de contraintes en C# via LINQ
2. **Comparer** les approches explicites (proprietes) vs implicites (arrays/lambdas)
3. **Utiliser** la theorie des tableaux Z3 (Select/Store) pour des structures de donnees dynamiques
4. **Construire** des modeles imbriques (tableaux 2D, grilles)
5. **Integrer** des sources de donnees heterogenes dans un theoreme hierarchique

## Contexte technique

**Z3.Linq** combine deux technologies :

- **Z3** : solveur SMT (*Satisfiability Modulo Theories*) capable de resoudre des contraintes sur des entiers, reels, booleens, tableaux et structures de donnees
- **LINQ** : syntaxe C# pour exprimer des requetes declarativement, automatiquement traduites en formules SMT par le binding

### Historique du projet

| Periode | Acteur | Contribution |
|---------|--------|-------------|
| 2015 | Ricardo Niepel | Base Z3.LinqBinding (LINQ -> Z3 binding) |
| 2018-2023 | jsboige | Arrays, hierarchical objects, nested arrays, meal planner |
| 2022-2023 | endjin | Modernisation .NET, CI, structure professionnelle |
| 2026 | MyIntelligenceAgency | Reintegration EPFdevelopment + serie pedagogique |

### Liens

- [endjin/Z3.Linq](https://github.com/endjin/Z3.Linq) (upstream)
- [MyIntelligenceAgency/Z3.Linq](https://github.com/MyIntelligenceAgency/Z3.Linq) (fork cette serie)
- [MyIntelligenceAgency/Z3.LinqBinding@EPFdevelopment](https://github.com/MyIntelligenceAgency/Z3.LinqBinding/tree/EPFdevelopment) (branche contributions jsboige)
- [Issue upstream #29](https://github.com/endjin/Z3.Linq/issues/29) (discussion contributions)

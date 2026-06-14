# Série Z3 - Programmation Déclarative avec Z3.Linq

**Navigation** : [Index SMT](../README.md) | [Index SymbolicAI](../../README.md) | [Index général](../../../README.md)

## Série en quelques mots

**6 notebooks** | **1 kernel** | **~4h30 de travail** | **Z3.Linq (.NET 9)**

**À qui s'adresse cette série** : étudiants en IA, développeurs C# souhaitant découvrir la programmation par contraintes, et tout curieux voulant comprendre comment exprimer un problème non pas comme un algorithme de résolution, mais comme un ensemble de contraintes que le solveur satisfait automatiquement. Aucun prérequis en logique formelle n'est supposé : les notebooks partent de théorèmes linéaires simples pour monter progressivement vers les théories de tableaux et l'optimisation hiérarchique.

## Présentation

**Z3** (Microsoft Research) est un solveur SMT (*Satisfiability Modulo Theories*) qui résout des systèmes de contraintes sur des entiers, des réels, des booléens et des tableaux. **Z3.Linq** est un binding qui traduit des expressions LINQ C# en formules SMT, permettant de modéliser des problèmes déclarativement sans écrire les appels Z3 bas niveau.

L'intérêt pédagogique : au lieu d'écrire un algorithme de backtracking pour un Sudoku ou un planificateur de repas, on décrit les contraintes (une seule valeur par case, pas de doublon par ligne, apports nutritionnels requis) et le solveur trouve les solutions. Ce changement de paradigme — de l'impératif au déclaratif — est au cœur de cette série.

### Déclaratif vs Impératif

| Aspect | Impératif (classique) | Déclaratif (Z3.Linq) |
|--------|----------------------|---------------------|
| **Approche** | Écrire l'algorithme de résolution | Décrire les contraintes, laisser le solveur résoudre |
| **Complexité** | Backtracking, heuristiques, pruning | Syntaxe LINQ naturelle en C# |
| **Évolution** | Modifier l'algorithme pour chaque nouveau problème | Ajouter des contraintes, le solveur s'adapte |
| **Vérification** | Tester les solutions | Les solutions satisfont les contraintes par construction |
| **Limite** | Difficile à généraliser | Performance sur les très grandes instances |

## Vue d'ensemble

| # | Notebook | Sujet | Durée | Statut |
|---|----------|-------|------|--------|
| 01 | [Linq2Z3 Intro](01_Linq2Z3_Intro.ipynb) | Théorèmes linéaires, Missionnaires-Cannibales, optimisation | ~45 min | PRODUCTION |
| 02 | [Sudoku Theorem vs Array](02_Sudoku_Theorem_vs_Array.ipynb) | Sudoku explicite (81 propriétés) vs implicite (`List<int>` + lambdas/closures) | ~50 min | PRODUCTION |
| 02b | [Sudoku Modes Comparison](02b_Sudoku_Modes_Comparison.ipynb) | **`CollectionHandling`** ressuscité : même Sudoku 4x4 résolu en mode `Array` vs `Constants` | ~25 min | BETA |
| 03 | [Array Theory](03_Array_Theory.ipynb) | Z3 array theory : Select/Store, switching dynamique | ~45 min | BETA |
| 04 | [Nested Arrays 2D](04_Nested_Arrays_2D.ipynb) | Tableaux imbriqués, grilles 2D, Sudoku 4x4, carré magique | ~40 min | BETA |
| 05 | [Meal Planner Hierarchical](05_Meal_Planner_Hierarchical.ipynb) | Planificateur de repas : data fusion LINQ + théorème hiérarchique | ~50 min | BETA |

### Fil pédagogique

1. **Notebook 01** pose les bases : le patron `Theorem<T>` de Z3.Linq, les théorèmes linéaires, la recherche de plus court chemin, et le classique Missionnaires-Cannibales
2. **Notebook 02** compare deux approches du Sudoku : 81 propriétés explicites vs modélisation implicite via arrays et lambdas
3. **Notebook 02b** démontre la feature ressuscitée `CollectionHandling` (mode `Array` vs `Constants`) sur un même Sudoku 4x4, preuve directe que l'enum précédemment morte est désormais câblée bout-en-bout
4. **Notebook 03** plonge dans la théorie des tableaux Z3 (Select/Store), avec switching dynamique entre représentations
5. **Notebook 04** généralise aux tableaux imbriqués (2D) : grilles, carrés magiques, Sudoku 4x4
6. **Notebook 05** intègre tout : data fusion LINQ + théorème hiérarchique multi-niveaux pour un planificateur de repas réaliste, et démontre le mode `CollectionHandling.Constants` (feature ressuscitée du fork)

## Prérequis

| Besoin | Détail |
|--------|--------|
| **.NET 9.0 SDK** | [Download](https://dotnet.microsoft.com/download/dotnet/9.0) |
| **.NET Interactive** | `dotnet tool install --global Microsoft.dotnet-interactive` |
| **Kernel Jupyter** | `.net-csharp` (installe automatiquement par .NET Interactive) |
| **Package NuGet** | `Z3.Linq` (NB-01, 02, 03 : charge automatiquement via `#r nuget:...`) |
| **NB-02b, 04, 05 — fork** | Les notebooks 02b, 04 et 05 utilisent le fork [MyIntelligenceAgency/Z3.Linq](https://github.com/MyIntelligenceAgency/Z3.Linq) : NB-04 pour le support `int[][]` (absent du NuGet public endjin), NB-02b et NB-05 pour la feature `CollectionHandling` (mode `Constants` ressuscité, câblée le 14/06/2026). Exécuter **une fois** : [`scripts/environment/z3-build-deploy.ps1`](../../../../scripts/environment/z3-build-deploy.ps1) (Windows) ou [`.sh`](../../../../scripts/environment/z3-build-deploy.sh) (Linux/macOS) — compile uniquement le wrapper (~1,5 s) et rassemble les 4 DLL dans `.deploy/`. |

> Les notebooks sont autonomes : le restore NuGet et l'initialisation du contexte Z3 sont inclus dans les cellules de setup de chaque notebook. **Exception** : les notebooks 02b, 04 et 05 chargent le fork via `#r "../Z3.Linq/.deploy/..."`, d'où le pré-requis du script de build ci-dessus (décision ai-01 [DECISION COORD] 2026-06-13, option (b), étendue à 02b/05 le 14/06/2026 pour `CollectionHandling`).

### Configuration : NuGet public vs fork

La série suit une stratégie à deux volets selon le besoin en tableaux imbriqués (`int[][]`) :

| Notebooks      | Source                 | Chargement                    | Pré-requis      |
|----------------|------------------------|-------------------------------|-----------------|
| 01, 02, 03     | NuGet public `Z3.Linq` | `#r nuget:Z3.Linq,...`        | Aucun (auto)    |
| 02b, 04, 05    | Fork (voir ci-dessus)  | `#r "../Z3.Linq/.deploy/..."` | Script de build |

**Pourquoi un fork pour le notebook 04 ?** Le support des tableaux imbriqués `int[][]` (construction de sort Z3 `Array Int (Array Int Int)`, extraction récursive `ExtractCollection`) provient de [Z3.LinqBinding@EPFdevelopment](https://github.com/MyIntelligenceAgency/Z3.LinqBinding/tree/EPFdevelopment) et n'existe pas dans le NuGet public endjin (`Z3.Linq` 2.0.1, qui ne gère qu'un seul niveau de collection). Publier un NuGet forké n'est pas possible (nous ne sommes pas propriétaires du *package-id*), d'où le script qui compile **uniquement** le wrapper fin et rassemble le solveur natif + les dépendances managées depuis le cache NuGet.

## Objectifs d'apprentissage

À l'issue de cette série, l'étudiant sera capable de :

1. **Modéliser** un problème de satisfaction de contraintes en C# via LINQ
2. **Comparer** les approches explicites (propriétés) vs implicites (arrays/lambdas)
3. **Utiliser** la théorie des tableaux Z3 (Select/Store) pour des structures de données dynamiques
4. **Construire** des modèles imbriqués (tableaux 2D, grilles)
5. **Intégrer** des sources de données hétérogènes dans un théorème hiérarchique

## Contexte technique

**Z3.Linq** combine deux technologies :

- **Z3** : solveur SMT (*Satisfiability Modulo Theories*) capable de résoudre des contraintes sur des entiers, réels, booléens, tableaux et structures de données
- **LINQ** : syntaxe C# pour exprimer des requêtes déclarativement, automatiquement traduites en formules SMT par le binding

### Historique du projet

| Période | Acteur | Contribution |
|---------|--------|-------------|
| 2015 | Ricardo Niepel | Base Z3.LinqBinding (LINQ -> Z3 binding) |
| 2018-2023 | jsboige | Arrays, hierarchical objects, nested arrays, meal planner |
| 2022-2023 | endjin | Modernisation .NET, CI, structure professionnelle |
| 2026 | MyIntelligenceAgency | Réintégration EPFdevelopment + série pédagogique |

### Liens

- [endjin/Z3.Linq](https://github.com/endjin/Z3.Linq) (upstream)
- [MyIntelligenceAgency/Z3.Linq](https://github.com/MyIntelligenceAgency/Z3.Linq) (fork cette série)
- [MyIntelligenceAgency/Z3.LinqBinding@EPFdevelopment](https://github.com/MyIntelligenceAgency/Z3.LinqBinding/tree/EPFdevelopment) (branche contributions jsboige)
- [Issue upstream #29](https://github.com/endjin/Z3.Linq/issues/29) (discussion contributions)

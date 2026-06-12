# Serie Z3 - Programmation Declarative avec Z3.Linq

**Navigation** : [Index SymbolicAI](../../README.md) | [Index general](../../../README.md)

## Description

Cette serie explore **Z3.Linq**, un binding LINQ pour le solveur SMT Z3 (Microsoft Research). Elle couvre la modelisation declarative de problemes de satisfaction de contraintes (CSP) en C#.

## Notebooks

| # | Notebook | Sujet | Statut |
|---|----------|-------|--------|
| 01 | [Linq2Z3 Intro](01_Linq2Z3_Intro.ipynb) | Introduction : theoremes lineaires, Missionnaires-Cannibales, optimisation | PRODUCTION |
<<<<<<< HEAD
| 02 | [Sudoku Theorem vs Array](02_Sudoku_Theorem_vs_Array.ipynb) | Sudoku explicite (81 proprietes) vs implicite (`List<int>` + lambdas/closures) | PRODUCTION |
| 03 | [Array Theory](03_Array_Theory.ipynb) | Z3 array theory avec switching dynamique | BETA |
| 04 | [Nested Arrays 2D](04_Nested_Arrays_2D.ipynb) | Tableaux imbriqués, grilles 2D, Sudoku 4x4, carré magique | BETA |
| 05 | [Meal Planner Hierarchical](05_Meal_Planner_Hierarchical.ipynb) | Planificateur de repas : data fusion LINQ + theoreme hierarchique | BETA |

## Prerequis

- **.NET 9.0** avec .NET Interactive (`dotnet tool install --global Microsoft.dotnet-interactive`)
- Kernel Jupyter `.net-csharp` installe
- Package NuGet `Z3.Linq` (charge automatiquement dans les notebooks)

## Contexte technique

**Z3.Linq** combine deux technologies :

- **Z3** : solveur SMT (Satisfiability Modulo Theories) capable de resoudre des contraintes sur des entiers, reels, tableaux et structures de donnees
- **LINQ** : syntaxe C# pour exprimer des requetes declarativement, automatiquement traduites en formules SMT

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

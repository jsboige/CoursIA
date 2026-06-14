# MetaGeneticSharp — Notebooks pédagogiques

[↑ Série Search](../README.md) | [↑ Entrée Partie 4](../Part4-Metaheuristics/README.md) | [Fork jsboige/MetaGeneticSharp →](https://github.com/jsboige/MetaGeneticSharp/blob/main/README.md)

Cinq notebooks .NET Interactive (C#) qui reconstruisent les métaheuristiques publiées à partir de **primitives composables** plutôt que comme des boîtes noires importées. Le fil conducteur : un algorithme doit pouvoir s'énoncer en quelques lignes déclaratives, et chaque brique (sélection, croisement, mutation, réinsertion) doit pouvoir être interceptée et recomposée.

Ces notebooks consomment la bibliothèque [MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) (sous-module voisin [`MetaGeneticSharp/`](https://github.com/jsboige/MetaGeneticSharp)) via ses DLLs buildées. Pour le positionnement de la Partie 4 (MGS vs GeneticSharp / mealpy / HeuristicLab, motivations pédagogique et ingénierie), voir l'[entrée Partie 4](../Part4-Metaheuristics/README.md).

## Parcours d'apprentissage

L'arc pédagogique va de l'application *d'une* métaheuristique à la **composition** de plusieurs, puis à la **structuration** de la population, et enfin à la **comparaison** honnête sur des benchmarks standard.

| # | Notebook | Concept clé | Primitives introduites |
|---|----------|-------------|------------------------|
| 1 | [MGS-1-Introduction](MGS-1-Introduction.ipynb) | Moteur autonome `MetaGeneticAlgorithm` | `DefaultMetaHeuristic`, `NoOp`, fitness quadratique |
| 2 | [MGS-2-Composition](MGS-2-Composition.ipynb) | Assemblage déclaratif | `Match`, contrôle-flux, grammaire fluente |
| 3 | [MGS-3-Eukaryote](MGS-3-Eukaryote.ipynb) | Sous-populations spécialisées | chromosomes composites, partitionnement |
| 4 | [MGS-4-Islands](MGS-4-Islands.ipynb) | Modèle insulaire | populations structurées, migration entre îles |
| 5 | [MGS-5-Benchmarks](MGS-5-Benchmarks.ipynb) | Comparaison honnête | `KnownFunctions`, composé WOA vs Uniform vs Islands |

### 1 — Introduction

Pourquoi un moteur autonome au-dessus de GeneticSharp ? Le notebook pose le contrat : un `MetaGeneticAlgorithm` qui pilote l'évolution sans dépendre de la classe `GeneticAlgorithm` amont, et un `IMetaHeuristic` qui intercepte chaque étape. On compare `DefaultMetaHeuristic` (reproduit le comportement GA classique) à `NoOp` (ne fait rien — l'observateur passif) sur un fitness quadratique simple. C'est le socle : tout le reste de la série compose au-dessus de ce moteur.

### 2 — Composition

Le cœur de la thèse « composants > métaphores ». On introduit `Match` (dispatch déclaratif sur le contexte d'évolution) et les primitives de contrôle-flux, puis on assemble une métaheuristique en quelques lignes lisibles. Ce notebook établit la grammaire fluente (`Match`, `Container`, `Scoped`) que WOA et EO réutiliseront plus tard comme briques plutôt que comme monolithes.

### 3 — Eukaryote

On cesse de traiter la population comme un sac homogène. Le modèle eucaryote partitionne la population en sous-populations spécialisées portées par des chromosomes composites — chaque compartiment peut avoir sa propre métaheuristique. C'est une configuration qu'aucune bibliothèque monolithique grand public n'offre directement, et qui devient naturelle une fois la composition maîtrisée.

### 4 — Islands

Le modèle insulaire structure la population en îles migratoires : chaque île évolue indépendamment, puis des individus migrent périodiquement. La primitive `IslandMetaHeuristic` assemble ce schéma à partir des mêmes briques que les notebooks précédents. La leçon : la diversité structurée (vs une population panmictique) change la dynamique de convergence.

### 5 — Benchmarks

La confrontation honnête. Dix fonctions standard (`KnownFunctions.cs` : Sphere, Rastrigin, Rosenbrock, Ackley, Griewank, Schwefel, Michalewicz, Zakharov, Booth, Dixon-Price) servent de paysages de test. On compare trois configurations — Uniform, WOA-reconstruit-depuis-les-primitives, Islands — et on rapporte les résultats sans trier les victoires : WOA gagne ou égalise sur 7/10, **diverge sur Schwefel** (le contrôle-flux géométrique sans clamp de bornes explose sur [-500, 500]). Cette divergence n'est pas un bug caché : l'inspectabilité du composé (on lit l'`IfElse` du bubble-net) en fait une démonstration de No-Free-Lunch, là où `mealpy` masquerait le mécanisme.

## Pré-requis & exécution

- **.NET 9.0** + le kernel `dotnet-interactive` (règle : pas de contournement, installer l'environnement complet). Voir la [configuration Partie 4](../Part4-Metaheuristics/README.md#configuration-requise).
- Les notebooks chargent les DLL du **checkout local du fork** via `#r "c:/dev/MetaGeneticSharp/..."`. Vérifier que `dotnet build` a produit les binaires sous `src/MetaGeneticSharp.Domain/bin/Debug/net9.0/` et `src/MetaGeneticSharp.Extensions/bin/Debug/net9.0/`.
- Règle C.2 : les notebooks sont committés **avec leurs outputs** (exécution réelle, kernel .NET).

## Conventions

- **Représentation agnostique.** Les composés géométriques (WOA, EO) requièrent un chromosome qui stocke les gènes en `double` de façon transparente. Les notebooks définissent un `DoubleArrayChromosome` (assistant de test, non livré dans la lib) avec `CreateNew()` randomisant dans les bornes — indispensable pour la diversité initiale d'un benchmark.
- **Fitness = négation.** GeneticSharp *maximise* le fitness ; chaque `Evaluate()` des fonctions benchmark renvoie donc l'objectif nié. La lib pinne cette convention par [tests unitaires](https://github.com/jsboige/MetaGeneticSharp/blob/main/tests/MetaGeneticSharp.Extensions.Tests/KnownFunctionsTests.cs) (optimum à x* + négation).

## Liens

- [Entrée Partie 4 — Metaheuristiques Composables](../Part4-Metaheuristics/README.md) — positionnement, objectifs, configuration
- [Fork jsboige/MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) — code source, tests (101), ROADMAP
- [Search-11-Metaheuristics](../Part1-Foundations/Search-11-Metaheuristics.ipynb) — introduction Python (PSO, ABC, SA, BRO)
- [Série Search](../README.md) — vue d'ensemble

# MetaGeneticSharp — Notebooks pédagogiques

[↑ Série Search](../README.md) | [↑ Entrée Partie 4](../Part4-Metaheuristics/README.md) | [Fork jsboige/MetaGeneticSharp →](https://github.com/jsboige/MetaGeneticSharp/blob/main/README.md)

Huit notebooks .NET Interactive (C#) qui reconstruisent les métaheuristiques publiées à partir de **primitives composables** plutôt que comme des boîtes noires importées. Le fil conducteur : un algorithme doit pouvoir s'énoncer en quelques lignes déclaratives, et chaque brique (sélection, croisement, mutation, réinsertion) doit pouvoir être interceptée et recomposée.

Ces notebooks consomment la bibliothèque [MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) (sous-module voisin [`MetaGeneticSharp/`](https://github.com/jsboige/MetaGeneticSharp)) via ses DLLs buildées. Pour le positionnement de la Partie 4 (MGS vs GeneticSharp / mealpy / HeuristicLab, motivations pédagogique et ingénierie), voir l'[entrée Partie 4](../Part4-Metaheuristics/README.md).

## Parcours d'apprentissage

L'arc pédagogique va de l'application *d'une* métaheuristique à la **composition** de plusieurs, puis à la **structuration** de la population, à la **comparaison** honnête sur des benchmarks standard, et enfin à la **généralité** de la grammaire (représentation combinatoire) et à la **visualisation** des paysages de fitness, y compris sur un relief terrestre réel.

| # | Notebook | Concept clé | Primitives introduites |
|---|----------|-------------|------------------------|
| 1 | [MGS-1-Introduction](MGS-1-Introduction.ipynb) | Moteur autonome `MetaGeneticAlgorithm` | `DefaultMetaHeuristic`, `NoOp`, fitness quadratique |
| 2 | [MGS-2-Composition](MGS-2-Composition.ipynb) | Assemblage déclaratif | `Match`, contrôle-flux, grammaire fluente |
| 3 | [MGS-3-Eukaryote](MGS-3-Eukaryote.ipynb) | Sous-populations spécialisées | chromosomes composites, partitionnement |
| 4 | [MGS-4-Islands](MGS-4-Islands.ipynb) | Modèle insulaire | populations structurées, migration entre îles |
| 5 | [MGS-5-Benchmarks](MGS-5-Benchmarks.ipynb) | Comparaison honnête | `KnownFunctions`, composé WOA vs Uniform vs Islands |
| 6 | [MGS-6-TSP](MGS-6-TSP.ipynb) | Grammaire agnostique à la représentation | `TspFitness`, `OrderedCrossover`, permutation + `Islands` |
| 7 | [MGS-7-LandscapeExplorer](MGS-7-LandscapeExplorer.ipynb) | Visualiser la surface de fitness | heatmaps PNG graphiques, 3 modes (fonction / carte d'altitude / image), trajectoire de convergence |
| 8 | [MGS-8-EverestRelief](MGS-8-EverestRelief.ipynb) | Relief terrestre réel comme paysage | `DemGrid` (DEM), interpolation bilinéaire, GA/WOA/EO vs PSO |

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

### 6 — TSP combinatoire

La grammaire de composition est-elle agnostique à la représentation ? MGS-1 à 5 opèrent sur des surfaces *continues* (gènes en `double`), mais les primitives structurantes (`Match`, `Container`, `Scoped`, `Islands`) vivent *sous* la couche géométrique. Ce notebook applique la **même** `IslandMetaHeuristic` à un problème de **permutation** — le Voyageur de Commerce sur 20 villes, gènes = index entiers — **sans aucune adaptation** : le modèle insulaire opère sur `IChromosome` et ne lit jamais `Gene.Value`. La comparaison reste honnête (G.9) : la baseline panmictique bat les Islands sur cette instance TSP-20, illustration de No-Free-Lunch — le point n'est pas la victoire mais le **transfert sans réécriture** de la grammaire d'une géométrie continue à un espace combinatoire. Setup : `TspFitness`, `OrderedCrossover` (OX1), `ReverseSequenceMutation`.

### 7 — Fitness Landscape Explorer

Tant que la surface de recherche est invisible, le choix d'une métaheuristique relève du doctrinal ; la visualiser le rend éclairé. Ce notebook consomme la bibliothèque `LandscapeRenderer` du fork — récupérée **byte-exact** depuis le *Landscape Explorer* original de jsboige (branche Metaheuristics @ `d05826fd`, PR giacomelli/GeneticSharp#87) — pour produire de **vraies heatmaps PNG graphiques** : `RenderHeatmap` peint chaque pixel selon la valeur de fitness (rampe rouge = haut / cyan = bas, minimum global Blanc, maximum global Noir) et `Plot` superpose les individus (BlueViolet) et le meilleur (Aqua). Trois modes de paysage sont couverts : **(1) fonction analytique** (les **vraies** `KnownFunctions`, p. ex. Sphere), **(2) carte d'altitude** — les **quatre cartes originales de jsboige** (Everest, Népal-Bhoutan, Plateau tibétain, Monde), récupérées byte-exact et embarquées comme ressources, lues comme champs de fitness via la verbatim `ImageHeightMapFunction` — et **(3) image custom** (un bitmap bimodal synthétique). La trajectoire de convergence du GA se superpose à la heatmap. Un wrapper `ShiftedFitness` translate l'optimum hors du centre pour rendre le **center-bias** visible : le GA converge sur l'optimum déplacé (≈ (2, 2)), preuve d'une recherche authentique. Les PNG sont encodés en base64 et affichés via `display(HTML(...))` — fiable sous papermill .NET (références DLL locales du fork, pas de `#r "nuget:"`).

### 8 — Trouver l'Everest : relief réel

L'aboutissement : le paysage n'est plus synthétique mais un **relief terrestre réel**. Une grille d'altitude (Digital Elevation Model, dérivée d'ETOPO1) est traitée comme une fonction de fitness à **maximiser** — *trouver l'Everest* = localiser le maximum global, sur quatre cartes à zoom croissant du globe entier à la région du sommet. La classe `DemGrid` ne fait que stocker la grille et interpoler (bilinéaire) ; aucune logique d'optimisation n'y vit. On lance le moteur MGS (GA / WOA / Equilibrium Optimizer) plus une baseline **PSO** externe à budget d'évaluations égal, et on mesure le **taux de réussite** de chaque méthode à localiser le sommet, relié au rapport taille-du-bassin / résolution. Rendu en **ASCII grayscale** (flux texte standard, fiable sous papermill .NET) — ce notebook reste sur un rendu texte, là où MGS-7 produit des heatmaps PNG graphiques.

## Pré-requis & exécution

- **.NET 9.0** + le kernel `dotnet-interactive` (règle : pas de contournement, installer l'environnement complet). Voir la [configuration Partie 4](../Part4-Metaheuristics/README.md#configuration-requise).
- Les notebooks chargent les DLL du **checkout local du fork** via `#r "c:/dev/MetaGeneticSharp/..."`. Vérifier que `dotnet build` a produit les binaires sous `src/MetaGeneticSharp.Domain/bin/Debug/net9.0/` et `src/MetaGeneticSharp.Extensions/bin/Debug/net9.0/`.
- Règle C.2 : les notebooks sont committés **avec leurs outputs** (exécution réelle, kernel .NET).

## Conventions

- **Représentation agnostique.** Les composés géométriques (WOA, EO) requièrent un chromosome qui stocke les gènes en `double` de façon transparente. Les notebooks définissent un `DoubleArrayChromosome` (assistant de test, non livré dans la lib) avec `CreateNew()` randomisant dans les bornes — indispensable pour la diversité initiale d'un benchmark.
- **Fitness = négation.** GeneticSharp *maximise* le fitness ; chaque `Evaluate()` des fonctions benchmark renvoie donc l'objectif nié. La lib pinne cette convention par [tests unitaires](https://github.com/jsboige/MetaGeneticSharp/blob/main/tests/MetaGeneticSharp.Extensions.Tests/KnownFunctionsTests.cs) (optimum à x* + négation).

## Liens

- [Entrée Partie 4 — Metaheuristiques Composables](../Part4-Metaheuristics/README.md) — positionnement, objectifs, configuration
- [Fork jsboige/MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) — code source, suite de tests unitaires, ROADMAP
- [Search-11-Metaheuristics](../Part1-Foundations/Search-11-Metaheuristics.ipynb) — introduction Python (PSO, ABC, SA, BRO)
- [Série Search](../README.md) — vue d'ensemble

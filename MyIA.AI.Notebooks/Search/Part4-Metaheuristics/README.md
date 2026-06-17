# Partie 4 : Metaheuristiques Composables (MetaGeneticSharp)

[↑ Série Search](../README.md) | [← Partie 2 : CSP](../Part2-CSP/README.md) | [Notebooks MGS →](MGS-1-Introduction.ipynb)

Comment passer de l'application *d'une* métaheuristique à la **composition** de plusieurs ? Cette partie ouvre la voie à [MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) — une bibliothèque .NET qui reconstruit les métaheuristiques publiées (Whale Optimization, Equilibrium Optimizer, modèle insulaire...) à partir de **primitives réutilisables** plutôt que comme des monolithes opaques. Neuf notebooks .NET Interactive (C#) en sont le fil conducteur : un algorithme doit pouvoir s'énoncer en quelques lignes déclaratives, et chaque brique (sélection, croisement, mutation, réinsertion) doit pouvoir être interceptée et recomposée.

Contrairement aux Parties 1 et 2 (notebooks Python avec OR-Tools, DEAP, mealpy), cette partie est un **side track C# .NET 9.0** : elle consomme GeneticSharp et la couche métaheuristique comme sous-modules, et s'exécute via le kernel `dotnet-interactive`. C'est le pont entre la série pédagogique Python et une vraie bibliothèque de code industrialisable — la démonstration que les concepts vus en Python (Search-5 génétique, Search-11 métaheuristiques) se retrouvent, solidement typés et composables, dans un runtime .NET. Les notebooks consomment la bibliothèque (sous-module voisin [`MetaGeneticSharp/`](../MetaGeneticSharp/)) via ses DLLs buildées.

## Pourquoi cette partie

Les Parties 1-2 enseignent à *choisir* une métaheuristique face à un problème ; cette partie enseigne à en *construire* et en *combiner*. La motivation est double :

- **Pédagogique.** Reconstruire WOA ou EO à partir de primitives (`Match`, `Container`, `Scoped`, contrôle-flux géométrique) force à comprendre *pourquoi* chaque étape existe — là où importer `mealpy` ou `scipy` masque le mécanisme derrière un appel de fonction. C'est le même réflexe qu'écrire un A* à la main avant d'utiliser `networkx`.
- **Ingénierie.** La composition ouvre des configurations qu'aucune bibliothèque monolithique n'offre directement : sous-populations spécialisées (Eukaryote), migration entre îles (Islands), métaheuristiques hybrides assemblées par grammaire fluente. Ces patterns existent dans la littérature mais sont rares dans les libs grand public.

L'enseignement transversal rejoint celui des Parties 1-2 : aucune métaheuristique ne domine partout (cf [Search-11](../Part1-Foundations/Search-11-Metaheuristics.ipynb)), et la bonne réponse à un problème d'optimisation est rarement « l'algorithme X » mais plutôt « la bonne composition de primitives pour ce paysage de fitness ».

## Positionnement : MetaGeneticSharp dans le paysage

| Bibliothèque | Langage | Représentation | Philosophie | Lien |
|--------------|---------|----------------|-------------|------|
| **MetaGeneticSharp** | C# .NET 9 | Agnostique (gènes = interfaces GeneticSharp) | **Composants > métaphores** : algorithmes reconstruits depuis des primitives composables | [jsboige/MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) |
| GeneticSharp | C# .NET | Agnostique (bit, permutation, arbre, float) | Bibliothèque GA classique, opérateurs en interfaces | [giacomelli/GeneticSharp](https://github.com/giacomelli/GeneticSharp) (sous-module, v3.1.4, non patché) |
| mealpy | Python | Vecteurs (continus surtout) | Catalogue large, tronc commun vectoriel, très compact | [thieu1995/mealpy](https://github.com/thieu1995/mealpy) |
| HeuristicLab | C# .NET | Plugin-based, GUI lourde | Plateforme d'expérimentation, optimisation interactive | [heal-research/HeuristicLab](https://github.com/heal-research/HeuristicLab) |

MetaGeneticSharp vise le point que les autres n'occupent pas : **l'expressivité déclarative de mealpy** (un algorithme en quelques lignes) **sur la représentation agnostique de GeneticSharp** (bit strings, permutations, arbres), sans sacrifier la performance. C'est le « child project » que [GeneticSharp PR #87](https://github.com/giacomelli/GeneticSharp/pull/87) suggérait de devenir : la couche métaheuristiques du PR, absorbée dans un moteur autonome au-dessus d'un GeneticSharp vanilla.

## Objectifs d'apprentissage

À l'issue de cette partie, vous serez capable de :

1. **Reconstruire** une métaheuristique publiée (WOA, EO) à partir de primitives composables plutôt que d'en importer une boîte noire
2. **Composer** des métaheuristiques via la grammaire fluente (`Match`, `Container`, `Scoped`) pour assembler des configurations hybrides
3. **Structurer** une population en sous-populations spécialisées (Eukaryote) ou en îles migratoires (Islands)
4. **Évaluer** quand une composition custom bat une métaheuristique monolithique sur un paysage de fitness donné

## Notebooks

Cette partie se compose de neuf notebooks .NET Interactive (C#), hébergés dans ce répertoire et consommant le sous-module voisin [`MetaGeneticSharp/`](../MetaGeneticSharp/) :

| # | Notebook | Concept clé | Primitives introduites | Durée |
|---|----------|-------------|------------------------|-------|
| 1 | [MGS-1-Introduction](MGS-1-Introduction.ipynb) | Moteur autonome `MetaGeneticAlgorithm` | `DefaultMetaHeuristic`, `NoOp`, fitness quadratique | ~40 min |
| 2 | [MGS-2-Composition](MGS-2-Composition.ipynb) | Assemblage déclaratif | `Match`, contrôle-flux, grammaire fluente | ~45 min |
| 3 | [MGS-3-Eukaryote](MGS-3-Eukaryote.ipynb) | Sous-populations spécialisées | chromosomes composites, partitionnement | ~50 min |
| 4 | [MGS-4-Islands](MGS-4-Islands.ipynb) | Modèle insulaire | populations structurées, migration entre îles | ~50 min |
| 5 | [MGS-5-CompoundMetaheuristics](MGS-5-CompoundMetaheuristics.ipynb) | Reconstruire les composés publiés (WOA/EO/FBI) | `MetaHeuristicsService`, `WhaleOptimisationAlgorithm`, `EquilibriumOptimizer`, factory `CreateMetaHeuristicByName` | ~50 min |
| 6 | [MGS-6-Benchmarks](MGS-6-Benchmarks.ipynb) | Comparaison honnête | `KnownFunctions`, composé WOA vs Uniform vs Islands | ~50 min |
| 7 | [MGS-7-TSP](MGS-7-TSP.ipynb) | Grammaire agnostique à la représentation | `TspFitness`, `OrderedCrossover`, permutation + `Islands` | ~45 min |
| 8 | [MGS-8-LandscapeExplorer](MGS-8-LandscapeExplorer.ipynb) | Visualiser la surface de fitness | heatmaps PNG graphiques, 3 modes (fonction / carte d'altitude / image), trajectoire de convergence | ~50 min |
| 9 | [MGS-9-EverestRelief](MGS-9-EverestRelief.ipynb) | Relief terrestre réel comme paysage | `DemGrid` (DEM), interpolation bilinéaire, GA/WOA/EO vs PSO | ~55 min |

La série couvre désormais l'arc complet : du moteur autonome (MGS-1) à la **reconstruction** des composés publiés depuis leurs primitives (MGS-5), puis à la comparaison sur benchmarks (MGS-6), à la **généralité** de la grammaire sur une représentation combinatoire (MGS-7) et à la **visualisation** des paysages de fitness, jusqu'à un relief terrestre réel (MGS-8/9). Descriptions détaillées notebook par notebook : voir « Parcours détaillé » ci-dessous. Feuille de route du fork : [ROADMAP.md](https://github.com/jsboige/MetaGeneticSharp/blob/main/ROADMAP.md).

## Parcours détaillé

### 1 — Introduction

Pourquoi un moteur autonome au-dessus de GeneticSharp ? Le notebook pose le contrat : un `MetaGeneticAlgorithm` qui pilote l'évolution sans dépendre de la classe `GeneticAlgorithm` amont, et un `IMetaHeuristic` qui intercepte chaque étape. On compare `DefaultMetaHeuristic` (reproduit le comportement GA classique) à `NoOp` (ne fait rien — l'observateur passif) sur un fitness quadratique simple. C'est le socle : tout le reste de la série compose au-dessus de ce moteur.

### 2 — Composition

Le cœur de la thèse « composants > métaphores ». On introduit `Match` (dispatch déclaratif sur le contexte d'évolution) et les primitives de contrôle-flux, puis on assemble une métaheuristique en quelques lignes lisibles. Ce notebook établit la grammaire fluente (`Match`, `Container`, `Scoped`) que WOA et EO réutiliseront plus tard comme briques plutôt que comme monolithes.

### 3 — Eukaryote

On cesse de traiter la population comme un sac homogène. Le modèle eucaryote partitionne la population en sous-populations spécialisées portées par des chromosomes composites — chaque compartiment peut avoir sa propre métaheuristique. C'est une configuration qu'aucune bibliothèque monolithique grand public n'offre directement, et qui devient naturelle une fois la composition maîtrisée.

### 4 — Islands

Le modèle insulaire structure la population en îles migratoires : chaque île évolue indépendamment, puis des individus migrent périodiquement. La primitive `IslandMetaHeuristic` assemble ce schéma à partir des mêmes briques que les notebooks précédents. La leçon : la diversité structurée (vs une population panmictique) change la dynamique de convergence.

### 5 — Métaheuristiques composées

D'où viennent les algorithmes « publiés » — Whale Optimization (WOA), Equilibrium Optimizer (EO), Forensic-Based Investigation (FBI) — et comment les utiliser sans retomber dans le piège de la boîte noire ? Ce notebook montre, pour chaque composé du catalogue, le même parcours en trois temps : **(1) la description** — la métaphore et la mécanique, dans l'esprit des fiches de `mealpy` ; **(2) la reconstruction depuis les primitives** — le corps réel de la méthode `BuildMainHeuristic()` qui assemble l'algorithme à partir de briques (`IfElse`, `Match`, `GenerationMetaHeuristic`, croisements géométriques), lu transparentement ; **(3) le raccourci factory** — le one-liner `MetaHeuristicsService.CreateMetaHeuristicByName("...")` qui produit *exactement* cette reconstruction, avec la preuve (le type racine renvoyé) que raccourci et reconstruction sont identiques. C'est l'argument « composants > métaphores » poussé jusqu'à la **preuve d'équivalence** : reconstruire un algorithme bio-inspiré *démontre* son mécanisme au lieu de le cacher derrière une métaphore animale (critique de Sørensen, 2015). Les benchmarks de MGS-6 mettent ensuite ces composés à l'épreuve.

### 6 — Benchmarks

La confrontation honnête. Dix fonctions standard (`KnownFunctions.cs` : Sphere, Rastrigin, Rosenbrock, Ackley, Griewank, Schwefel, Michalewicz, Zakharov, Booth, Dixon-Price) servent de paysages de test. On compare trois configurations — Uniform, WOA-reconstruit-depuis-les-primitives, Islands — et on rapporte les résultats sans trier les victoires : WOA gagne ou égalise sur 7/10, **diverge sur Schwefel** (le contrôle-flux géométrique sans clamp de bornes explose sur [-500, 500]). Cette divergence n'est pas un bug caché : l'inspectabilité du composé (on lit l'`IfElse` du bubble-net) en fait une démonstration de No-Free-Lunch, là où `mealpy` masquerait le mécanisme.

### 7 — TSP combinatoire

La grammaire de composition est-elle agnostique à la représentation ? MGS-1 à 6 opèrent sur des surfaces *continues* (gènes en `double`), mais les primitives structurantes (`Match`, `Container`, `Scoped`, `Islands`) vivent *sous* la couche géométrique. Ce notebook applique la **même** `IslandMetaHeuristic` à un problème de **permutation** — le Voyageur de Commerce sur 20 villes, gènes = index entiers — **sans aucune adaptation** : le modèle insulaire opère sur `IChromosome` et ne lit jamais `Gene.Value`. La comparaison reste honnête (G.9) : la baseline panmictique bat les Islands sur cette instance TSP-20, illustration de No-Free-Lunch — le point n'est pas la victoire mais le **transfert sans réécriture** de la grammaire d'une géométrie continue à un espace combinatoire. Setup : `TspFitness`, `OrderedCrossover` (OX1), `ReverseSequenceMutation`.

### 8 — Fitness Landscape Explorer

Tant que la surface de recherche est invisible, le choix d'une métaheuristique relève du doctrinal ; la visualiser le rend éclairé. Ce notebook consomme la bibliothèque `LandscapeRenderer` du fork — récupérée **byte-exact** depuis le *Landscape Explorer* original de jsboige (branche Metaheuristics @ `d05826fd`, PR giacomelli/GeneticSharp#87) — pour produire de **vraies heatmaps PNG graphiques** : `RenderHeatmap` peint chaque pixel selon la valeur de fitness (rampe rouge = haut / cyan = bas, minimum global Blanc, maximum global Noir) et `Plot` superpose les individus (BlueViolet) et le meilleur (Aqua). Trois modes de paysage sont couverts : **(1) fonction analytique** (les **vraies** `KnownFunctions`, p. ex. Sphere), **(2) carte d'altitude** — les **quatre cartes originales de jsboige** (Everest, Népal-Bhoutan, Plateau tibétain, Monde), récupérées byte-exact et embarquées comme ressources, lues comme champs de fitness via la verbatim `ImageHeightMapFunction` — et **(3) image custom** (un bitmap bimodal synthétique). La trajectoire de convergence du GA se superpose à la heatmap. Un wrapper `ShiftedFitness` translate l'optimum hors du centre pour rendre le **center-bias** visible : le GA converge sur l'optimum déplacé (≈ (2, 2)), preuve d'une recherche authentique. Les PNG sont encodés en base64 et affichés via `display(HTML(...))` — fiable sous papermill .NET (références DLL locales du fork, pas de `#r "nuget:"`).

### 9 — Trouver l'Everest : relief réel

L'aboutissement : le paysage n'est plus synthétique mais un **relief terrestre réel**. Une grille d'altitude (Digital Elevation Model, dérivée d'ETOPO1) est traitée comme une fonction de fitness à **maximiser** — *trouver l'Everest* = localiser le maximum global, sur quatre cartes à zoom croissant du globe entier à la région du sommet. La classe `DemGrid` ne fait que stocker la grille et interpoler (bilinéaire) ; aucune logique d'optimisation n'y vit. On lance le moteur MGS (GA / WOA / Equilibrium Optimizer) plus une baseline **PSO** externe à budget d'évaluations égal, et on mesure le **taux de réussite** de chaque méthode à localiser le sommet, relié au rapport taille-du-bassin / résolution. Rendu en **heatmaps PNG graphiques** via le même `SkiaLandscapeRenderer` du fork que MGS-8 (cohérence intra-série), avec la **cible inversée** : MGS-8 *minimise* ses fonctions analytiques (l'optimum porte le marqueur Blanc) ; MGS-9 *maximise* l'altitude, donc c'est le **sommet** qui porte le **marqueur Noir** — la cible explicite de la recherche.

## Configuration requise

Ces notebooks requièrent **.NET 9.0** et le kernel `dotnet-interactive` (règle : pas de contournement, installer l'environnement complet) :

```powershell
# 1. .NET 9 SDK (si manquant)
dotnet --version  # doit afficher 9.x

# 2. dotnet-interactive (kernel Jupyter pour C#)
dotnet tool install --global Microsoft.dotnet-interactive
dotnet interactive jupyter install

# 3. Sous-modules + build du fork (les notebooks chargent les DLL par #r absolu)
cd MyIA.AI.Notebooks/Search/MetaGeneticSharp
git submodule update --init --recursive
dotnet build
```

Les notebooks chargent les DLL via `#r "c:/dev/MetaGeneticSharp/..."` (chemin du checkout de travail du fork). Vérifiez que `dotnet build` a produit les binaires sous `src/MetaGeneticSharp.Domain/bin/Debug/net9.0/` et `src/MetaGeneticSharp.Extensions/bin/Debug/net9.0/`.

Règle C.2 : les notebooks sont committés **avec leurs outputs** (exécution réelle, kernel .NET).

## Conventions

- **Représentation agnostique.** Les composés géométriques (WOA, EO) requièrent un chromosome qui stocke les gènes en `double` de façon transparente. Les notebooks définissent un `DoubleArrayChromosome` (assistant de test, non livré dans la lib) avec `CreateNew()` randomisant dans les bornes — indispensable pour la diversité initiale d'un benchmark.
- **Fitness = négation.** GeneticSharp *maximise* le fitness ; chaque `Evaluate()` des fonctions benchmark renvoie donc l'objectif nié. La lib pinne cette convention par [tests unitaires](https://github.com/jsboige/MetaGeneticSharp/blob/main/tests/MetaGeneticSharp.Extensions.Tests/KnownFunctionsTests.cs) (optimum à x* + négation).

## Boucle CoursIA ↔ fork

Le code de la bibliothèque vit dans le **fork** [jsboige/MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp), monté ici comme sous-module (`MyIA.AI.Notebooks/Search/MetaGeneticSharp/`). Les notebooks pédagogiques (ce répertoire) sont propriété du dépôt CoursIA et consomment la bibliothèque via ses DLLs buildées. Ce point d'entrée ferme la boucle : depuis la série Search Python (Parties 1-2), on bascule vers le side track C#, qui redirige à son tour vers le fork pour le code source complet, les tests et la feuille de route.

## Références

Les métaheuristiques reconstruites dans cette partie suivent les articles fondateurs. Les liens bibliothèque (GeneticSharp, fork MGS) sont regroupés dans la section « Liens » ci-dessous.

| Notebook(s) | Métaheuristique | Référence |
|-------------|-----------------|-----------|
| MGS-1 (Introduction) | Algorithme génétique | Holland, J. H. (1975) — *Adaptation in Natural and Artificial Systems*. University of Michigan Press. |
| MGS-5 (Compound), MGS-6 (Benchmarks) | Whale Optimization Algorithm | Mirjalili, S., & Lewis, A. (2016) — « The Whale Optimization Algorithm », *Advances in Engineering Software* 95. |
| MGS-5 (Compound), MGS-9 (EverestRelief) | Equilibrium Optimizer | Faramarzi, A., Heidarinejad, M., Stephens, B., & Mirjalili, S. (2020) — « Equilibrium optimizer: A novel optimization algorithm », *Knowledge-Based Systems* 197. |
| MGS-9 (EverestRelief) | Particle Swarm Optimization (baseline) | Kennedy, J., & Eberhart, R. (1995) — « Particle Swarm Optimization », *Proc. IEEE Int. Conf. on Neural Networks*. |
| MGS-6, MGS-7 | No-Free-Lunch | Wolpert, D. H., & Macready, W. G. (1997) — « No free lunch theorems for optimization », *IEEE Trans. on Evolutionary Computation* 1(1). |

## Liens

- [Fork jsboige/MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) — code source, tests, ROADMAP
- [GeneticSharp PR #87](https://github.com/giacomelli/GeneticSharp/pull/87) — origine du projet (couche métaheuristiques 2020-2022)
- [Search-11-Metaheuristics](../Part1-Foundations/Search-11-Metaheuristics.ipynb) — introduction Python (PSO, ABC, SA, BRO) et benchmarks comparatifs
- [Série Search](../README.md) — vue d'ensemble

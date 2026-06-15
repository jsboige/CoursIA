# Partie 4 : Metaheuristiques Composables (MetaGeneticSharp)

[↑ Série Search](../README.md) | [← Partie 2 : CSP](../Part2-CSP/README.md) | [Notebooks MGS →](../MetaGeneticSharp-Notebooks/MGS-1-Introduction.ipynb)

Comment passer de l'application *d'une* métaheuristique à la **composition** de plusieurs ? Cette partie ouvre la voie à [MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) — une bibliothèque .NET qui reconstruit les métaheuristiques publiées (Whale Optimization, Equilibrium Optimizer, modèle insulaire...) à partir de **primitives réutilisables** plutôt que comme des monolithes opaques. Le fil rouge est un changement de perspective : un algorithme doit pouvoir s'énoncer en quelques lignes déclaratives, et chaque brique (sélection, croisement, mutation, réinsertion) doit pouvoir être interceptée et recomposée.

Contrairement aux Parties 1 et 2 (notebooks Python avec OR-Tools, DEAP, mealpy), cette partie est un **side track C# .NET 9.0** : elle consomme GeneticSharp et la couche métaheuristique comme sous-modules, et s'exécute via le kernel `dotnet-interactive`. C'est le pont entre la série pédagogique Python et une vraie bibliothèque de code industrialisable — la démonstration que les concepts vus en Python (Search-5 génétique, Search-11 métaheuristiques) se retrouvent, solidement typés et composables, dans un runtime .NET.

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

Cette partie s'appuie sur les notebooks .NET Interactive du répertoire voisin [`MetaGeneticSharp-Notebooks/`](../MetaGeneticSharp-Notebooks/) (le code pédagogique vit à côté du code de la bibliothèque, dans le sous-module) :

| # | Notebook | Contenu | Durée |
|---|----------|---------|-------|
| 1 | [MGS-1-Introduction](../MetaGeneticSharp-Notebooks/MGS-1-Introduction.ipynb) | `MetaGeneticAlgorithm`, moteur autonome, `DefaultMetaHeuristic` vs `NoOp`, fitness quadratique | ~40 min |
| 2 | [MGS-2-Composition](../MetaGeneticSharp-Notebooks/MGS-2-Composition.ipynb) | Primitives de composition : `Match`, contrôle-flux, assemblage déclaratif | ~45 min |
| 3 | [MGS-3-Eukaryote](../MetaGeneticSharp-Notebooks/MGS-3-Eukaryote.ipynb) | Sous-populations, chromosomes composites, partitionnement spécialisé | ~50 min |
| 4 | [MGS-4-Islands](../MetaGeneticSharp-Notebooks/MGS-4-Islands.ipynb) | Modèle insulaire, populations structurées, migration entre îles | ~50 min |
| 5 | [MGS-5-Benchmarks](../MetaGeneticSharp-Notebooks/MGS-5-Benchmarks.ipynb) | Comparaison honnête : Uniform vs WOA-from-primitives vs Islands sur 10 fonctions (`KnownFunctions`), No-Free-Lunch | ~50 min |
| 6 | [MGS-6-TSP](../MetaGeneticSharp-Notebooks/MGS-6-TSP.ipynb) | La grammaire de composition est agnostique à la représentation : `Islands` sur un chromosome de permutation (TSP), sans adaptation | ~45 min |
| 7 | [MGS-7-LandscapeExplorer](../MetaGeneticSharp-Notebooks/MGS-7-LandscapeExplorer.ipynb) | Visualiser la surface de fitness (revival gtk#) : heatmap ASCII, projection 2D, trajectoire de convergence, center-bias | ~50 min |
| 8 | [MGS-8-EverestRelief](../MetaGeneticSharp-Notebooks/MGS-8-EverestRelief.ipynb) | Un relief terrestre réel (DEM) comme paysage à maximiser : GA/WOA/EO vs baseline PSO, taux de réussite | ~55 min |

La série couvre désormais l'arc complet : du moteur autonome (MGS-1) à la comparaison sur benchmarks (MGS-5), puis à la **généralité** de la grammaire sur une représentation combinatoire (MGS-6) et à la **visualisation** des paysages de fitness, jusqu'à un relief terrestre réel (MGS-7/8). Vue d'ensemble et descriptions détaillées : [`MetaGeneticSharp-Notebooks/README.md`](../MetaGeneticSharp-Notebooks/README.md). Feuille de route du fork : [ROADMAP.md](https://github.com/jsboige/MetaGeneticSharp/blob/main/ROADMAP.md).

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

Les notebooks chargent les DLL via `#r "c:/dev/MetaGeneticSharp/..."` (chemin du checkout de travail du fork). Vérifiez que `dotnet build` a produit les binaires sous `src/MetaGeneticSharp.Domain/bin/Debug/net9.0/`.

## Boucle CoursIA ↔ fork

Le code de la bibliothèque vit dans le **fork** [jsboige/MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp), monté ici comme sous-module (`MyIA.AI.Notebooks/Search/MetaGeneticSharp/`). Les notebooks pédagogiques (`MetaGeneticSharp-Notebooks/`) sont propriété du dépôt CoursIA et consomment la bibliothèque via ses DLLs buildées. Ce point d'entrée ferme la boucle : depuis la série Search Python (Parties 1-2), on bascule vers le side track C#, qui redirige à son tour vers le fork pour le code source complet, les tests et la feuille de route.

## Liens

- [Fork jsboige/MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) — code source, tests, ROADMAP
- [GeneticSharp PR #87](https://github.com/giacomelli/GeneticSharp/pull/87) — origine du projet (couche métaheuristiques 2020-2022)
- [Search-11-Metaheuristics](../Part1-Foundations/Search-11-Metaheuristics.ipynb) — introduction Python (PSO, ABC, SA, BRO) et benchmarks comparatifs
- [Série Search](../README.md) — vue d'ensemble

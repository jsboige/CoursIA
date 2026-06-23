# Partie 4 : Metaheuristiques Composables (MetaGeneticSharp)

[↑ Série Search](../README.md) | [← Partie 2 : CSP](../Part2-CSP/README.md) | [Notebooks MGS →](MGS-1-Introduction.ipynb)

Comment passer de l'application *d'une* métaheuristique à la **composition** de plusieurs ? Cette partie ouvre la voie à [MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) — une bibliothèque .NET qui reconstruit les métaheuristiques publiées (Whale Optimization, Equilibrium Optimizer, Differential Evolution, Bare-Bones PSO, modèle insulaire...) à partir de **primitives réutilisables** plutôt que comme des monolithes opaques. Douze notebooks .NET Interactive (C#) en sont le fil conducteur : un algorithme doit pouvoir s'énoncer en quelques lignes déclaratives, et chaque brique (sélection, croisement, mutation, réinsertion) doit pouvoir être interceptée et recomposée.

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

Cette partie se compose de douze notebooks .NET Interactive (C#), hébergés dans ce répertoire et consommant le sous-module voisin [`MetaGeneticSharp/`](../MetaGeneticSharp/) :

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
| 9 | [MGS-9-EverestRelief](MGS-9-EverestRelief.ipynb) | Relief terrestre réel comme paysage | `DemGrid` (wrapper `ImageHeightMapFunction`), cartes `KnownHeightMap` de jsboige, GA/WOA/EO vs PSO, flipbook de convergence | ~55 min |
| 10 | [MGS-10-CenterBias](MGS-10-CenterBias.ipynb) | Biais central vs robustesse au déplacement | banc `CenterBiasBenchmark` (Kudela 2022), composés WOA/EO/FBI/DE/BBPSO/SA vs GA/Random, signature $\Delta$ | ~45 min |
| 11 | [MGS-11-IslandSynergy](MGS-11-IslandSynergy.ipynb) | Synergie d'îles complémentaires (verdict mesuré) | `IslandCompoundMetaheuristic`, archipel hétérogène DE+BBPSO, dé-biais `ShiftedFitness`, GIF multicolore par île | ~45 min |
| 12 | [MGS-12-AxisAlignment](MGS-12-AxisAlignment.ipynb) | Biais d'alignement d'axes (rotation) | décorateur `RotatedFitness` ($M x$, Givens orthogonale), séparabilité vs rotation, optimum relocalisé, signature $\Delta$ | ~45 min |

La série couvre désormais l'arc complet : du moteur autonome (MGS-1) à la **reconstruction** des composés publiés depuis leurs primitives (MGS-5), puis à la comparaison sur benchmarks (MGS-6), à la **généralité** de la grammaire sur une représentation combinatoire (MGS-7) et à la **visualisation** des paysages de fitness, jusqu'à un relief terrestre réel (MGS-8/9), puis à la **caractérisation empirique du biais central** des composés (MGS-10) et à la **mesure falsifiable d'une synergie** d'îles hétérogènes (MGS-11), enfin au **second biais des bancs CEC** : l'alignement d'axes par rotation du paysage (MGS-12). Descriptions détaillées notebook par notebook : voir « Parcours détaillé » ci-dessous. Feuille de route du fork : [ROADMAP.md](https://github.com/jsboige/MetaGeneticSharp/blob/main/ROADMAP.md).

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

L'aboutissement : le paysage n'est plus synthétique mais un **relief terrestre réel**, et en **vraie résolution**. Les quatre cartes d'altitude sont les **assets verbatim de jsboige** (`KnownHeightMap.{World, TibetanPlateau, NepalBhoutan, EverestMount}`, PNG ~2560 px, acquis à l'origine depuis un service d'élévation WMS) — récupérés **byte-exact** sur le fork @ `d05826fd` et lus par la classe verbatim `ImageHeightMapFunction` (niveaux de gris = altitude, interpolation inverse-distance). Pas de grille `int[]` rééchantillonnée, pas de downsampling ETOPO1 : le PNG haute-définition **est** le champ de fitness. La classe pédagogique `DemGrid` n'est qu'une enveloppe *drop-in* sur `ImageHeightMapFunction` (elle expose `Interp`/`GlobalMax`/`ElevMin`/`ElevMax`) ; aucune logique d'optimisation n'y vit. On **maximise** le niveau de gris — le pixel le plus clair est le sommet — sur quatre cartes à zoom croissant (Monde → Plateau → Himalaya → Everest : le pic se resserre à mesure qu'on zoome). On lance le moteur MGS (GA / WOA / Equilibrium Optimizer) plus une baseline **PSO** externe à budget d'évaluations égal, et on mesure le **taux de réussite** de chaque méthode à localiser le sommet, relié au rapport taille-du-bassin / résolution. Un **flipbook de convergence** (même orchestration `GenerationRan` qu'en MGS-8) montre ensuite la population se contracter génération après génération vers le sommet sur la région Everest. Rendu en **heatmaps PNG graphiques** via le même `SkiaLandscapeRenderer` du fork que MGS-8 (cohérence intra-série, rendu SkiaSharp cross-platform), avec la **cible inversée** : MGS-8 *minimise* ses fonctions analytiques (l'optimum porte le marqueur Blanc) ; MGS-9 *maximise* l'altitude, donc c'est le **sommet** qui porte le **marqueur Noir** — la cible explicite de la recherche.

### 10 — Biais central

MGS-6 montrait qu'aucune métaheuristique publiée ne bat la composition en performance brute ; MGS-10 ajoute une **seconde preuve**, plus profonde, en mesurant un défaut que la performance masque : le **biais central**. Le notebook câble le banc `CenterBiasBenchmark` du fork (protocole *centré-vs-déplacé* de Kudela, 2022) : chaque optimiseur est lancé sur une même fonction (Sphere, Rastrigin, Ackley ; dimension 5, NFE = 5000) en deux versions, l'optimum au **centre** puis **relocalisé** hors centre via `ShiftedFitness`. La signature $\Delta = f^\star_{\text{déplacé}} - f^\star_{\text{centré}}$ révèle si l'optimiseur résout la fonction *où que soit l'optimum* ($\Delta \approx 0$, non biaisé — la recherche aléatoire uniforme en est le contrôle canonique) ou s'il n'exploite que le placement central ($\Delta \gg 0$, biaisé vers le centre). Huit optimiseurs sont confrontés : **Random** (contrôle *seedé* `seed:7`, la référence non biaisée), **GA**, et les six composés géométriques **WOA, EO, FBI, Differential Evolution, Bare-Bones PSO, Recuit simulé** (Metropolis, 1953 ; Kirkpatrick, Gelatt & Vecchi, 1983). **Reproductibilité.** Le banc est **seedé** : `FastRandomRandomization.ResetSeed(masterSeed)` ancre le RNG global du framework une fois avant la suite, de sorte que les chiffres committés sont **reproduisibles** d'une exécution à l'autre — un étudiant qui ré-exécute le notebook retrouve exactement la table ci-dessous (le contrôle `Random` reste seedé séparément, `seed: 7`).

Lecture honnête (G.9), fonction par fonction. **Sphere** (unimodale lisse) : tous les optimiseurs résolvent les deux cas (~0) → $\Delta \approx 0$ partout ; fonction trop facile pour révéler un biais. **Rastrigin** (fortement multimodale) : les $\Delta$ sont **bruités** — le contrôle Random lui-même y affiche le $\Delta$ le plus élevé (+7,9) ; à NFE = 5000 l'optimiseur tombe dans un optimum local différent selon le tirage, donc le $\Delta$ y mesure de la variance d'échantillonnage, pas un biais directionnel (la colonne *moyenne* qui agrège les trois fonctions est dominée par ce bruit et n'est pas un signal fiable). **Ackley** (puits central entouré de rides — la fonction *conçue* pour exposer le biais central) : **seul WOA** affiche $\Delta \gg 0$ (+4,36) — il résout Ackley centrée (~0) mais **rate** Ackley déplacée (4,36), signant un biais central net ; tous les autres (GA, EO, FBI, DE, BBPSO, Recuit simulé) résolvent les deux cas (~0) et sont **robustes** au déplacement. Leçon affûtée de « composants > métaphores » : ce n'est pas l'étiquette métaphorique (baleine, équilibre, criminalistique) qui prédit le biais — EO, FBI et BBPSO sont eux aussi « métaphoriques » mais robustes — c'est la **structure de l'opérateur**. L'encerclement de la meilleure position (le *bubble-net* de WOA) ancre la recherche sur le meilleur courant, qui sur une fonction à optimum central démarre près du centre → biais. Les opérateurs d'exploration arithmétique (**DE**, $v = r_1 + F \cdot (r_2 - r_3)$, même couche géométrique `GeometricCrossover`/`MatchMetaHeuristic` que WOA) et la perturbation gaussienne isotrope du **Recuit simulé** (critère de Metropolis) n'ancrent pas → robustesse. Ce n'est donc pas l'étiquette « métaphore » qui biaise vers le centre, mais l'ancrage de l'opérateur à un attracteur géométrique fixe. Leçon de lecture (honnêteté, G.9) : un $\Delta$ élevé n'est un *biais* que si l'optimiseur résolvait effectivement le cas centré ; sinon il signe juste de la faiblesse — d'où trois exercices (stabilité multi-graine de la signature, balayage de l'amplitude du déplacement, extension de la suite à Rosenbrock et Griewank).

### 11 — Synergie d'îles complémentaires

La composition est-elle **magique** ? Combiner un bon explorateur et un bon exploiteur dans un archipel hétérogène produit-il mécaniquement une synergie ? Ce notebook pose la question de façon **falsifiable** et y répond chiffres à l'appui. On assemble trois archipels de **même structure** (4 îles, migration `SmallMigrationRate`) via `IslandCompoundMetaheuristic` — (a) îles DE homogènes, (b) îles BBPSO homogènes, (c) 2 îles DE + 2 îles BBPSO hétérogène — et on les lance, à budget d'évaluations égal, sur Rastrigin et Ackley **dé-biaisées** en dimension 5 (optimum relocalisé hors centre via `ShiftedFitness` + `ShiftVectors.Seeded`). La dimension 5 (et non 2) est choisie pour que les opérateurs *différencient* : en dim 2, tous résolvent Rastrigin (objectif 0), rendant une synergie indiscernable. Un **GIF multicolore** (overlay `individualColors` + `EncodeAnimatedGif`) colore chaque individu par son île (DE en orange, BBPSO en vert) : la répartition exploration / exploitation devient visible génération après génération. **Verdict honnête (résultat négatif)** : sur les deux fonctions, l'archipel hétérogène est **battu** par le meilleur de ses constituants (0/2 synergie) — la migration entre opérateurs dissemblables peut *propager les solutions piégées* et produire un compromis *inférieur* au meilleur constituant. La synergie d'îles n'est pas automatique : elle se démontre, ne se décrète pas — la même leçon « composants > métaphores » (Sorensen 2015) poussée jusqu'à la *mesure* de la composition. Caveats : graine unique (pas un banc multi-graines ; banc rigoureux rote = #3963), GIF 2D illustratif alors que le banc est en dim 5.

### 12 — Alignement d'axes

MGS-10 instrumentait le biais **central** (un optimum à l'origine flatte les optimiseurs qui démarrent au centre) ; ce notebook instrumente le biais **complémentaire** des bancs CEC : l'**alignement d'axes**. On introduit le décorateur compositionnel `RotatedFitness` du fork — l'analogue de `ShiftedFitness` pour la rotation — qui évalue la fonction interne sur des coordonnées rotationnées $f_{\text{rot}}(x) = f(M x)$, où $M$ est une matrice orthogonale ($M M^\top = I$) fabriquée par le factory `RotationMatrices.Seeded(n, seed)` comme **produit de rotations de Givens** (orthogonale par construction, reproductible par $(n, \text{seed})$). Comme `ShiftedFitness`, c'est un décorateur fin : les mathématiques des fonctions canoniques sont réutilisées telles quelles (jamais réimplémentées), seules les coordonnées sont linéairement transformées.

La **partie A** valide le décorateur contre la géométrie : sur Sphere (purement radiale, invariante par construction) la rotation est un no-op ; sur Rastrigin (terme $\sum \cos(2\pi x_i)$ séparable, un cosinus par axe) la rotation brise la séparabilité — la rotation *mesure* donc la séparabilité d'une fonction, c'est exactement pourquoi les suites CEC les rotationnent. La **partie B** montre la discrimination géométrique : sur Rosenbrock (asymétrique, vallée banane), la rotation conserve la *valeur* de l'optimum ($\approx 0$) mais en **déplace la position** — l'optimiseur aligné sur les axes ne peut plus descendre coordonnée par coordonnée.

La **partie C** confronte les optimiseurs au banc : signature $\Delta = f^\star_{\text{roté}} - f^\star_{\text{non roté}}$ (le RNG est reseedé avant chaque paire pour isoler l'effet du paysage, pas du hasard). **Lecture honnête (G.9)** : en dimension 2 et à ce budget, $\Delta \approx 0$ pour **tous** — Rosenbrock 2D est assez facile pour que GA, WOA, DE, BBPSO la résolvent à zéro, rotationnée ou non ; il n'y a alors **pas de marge** pour qu'un alignement sur les axes pénalise. Un banc honnête ne « prouve » un biais opérateur que si le problème est assez dur pour que le biais ait de la place pour se manifester : ici le signal net est dans la **géométrie du paysage** (parties A/B), et complexifier le problème (dimension plus élevée, budget plus serré) pour révéler l'effet *opérateur* — un $\Delta$ qui sépare les déplacements composante par composant (crossover uniforme, WOA) des déplacements vectoriels (DE) — est précisément l'objet de l'exercice 2. On retrouve l'esprit de MGS-10 : on juge un optimiseur sur la **structure de ses opérateurs** (vectoriels vs composante par composant, centrés vs non), pas sur le nom de sa métaphore — et un banc honnête doit tester les **deux** biais CEC (`ShiftedFitness` + `RotatedFitness`, composables en la variante CEC complète `new RotatedFitness(new ShiftedFitness(inner, o), M)`).

## Configuration requise

Le kernel `dotnet-interactive` (version pinnée **1.0.552801**) est un **hôte .NET 8.0** : il ne peut pas charger d'assemblies compilées en `net9.0` (`System.Runtime 9.0.0.0` introuvable à l'exécution). Les notebooks MGS se répartissent donc sur deux TFM :

- **MGS-1 à MGS-5** (Introduction, Composition, Eukaryote, Islands, Compound) ne consomment que `MetaGeneticSharp.Domain` + `Infrastructure` + `GeneticSharp`. Ils référencent les **DLL `net8.0`** et s'exécutent sur le kernel pinné.
- **MGS-6 à MGS-9** (Benchmarks, TSP, Landscape, Everest) dépendent en plus de `MetaGeneticSharp.Extensions` (SkiaSharp / `System.Drawing.Common`), non encore buildé pour `net8.0`. Ils référencent les DLL `net9.0` et restent **bloqués sur le kernel pinné** (follow-up : builder `Extensions` pour `net8.0`, ou multi-targeter le fork).

Règle : pas de contournement, installer l'environnement complet :

```powershell
# 1. .NET SDK (8.0 pour le kernel pinné ; 9.0 pour le fork source)
dotnet --version

# 2. dotnet-interactive (kernel Jupyter pour C#, hôte net8.0)
dotnet tool install --global Microsoft.dotnet-interactive
dotnet interactive jupyter install

# 3. Sous-modules + build du fork (les notebooks chargent les DLL par #r absolu)
cd MyIA.AI.Notebooks/Search/MetaGeneticSharp
git submodule update --init --recursive
dotnet build                      # build net9.0 (fork source ; DLLs pour MGS-6..9)
```

> **Bins `net8.0` pour MGS-1..5.** Le fork est actuellement single-TFM `net9.0`, donc `-p:TargetFramework=net8.0` échoue (le `project.assets.json` restauré ne contient que la cible net9.0). Pour produire `Domain` + `Infrastructure` en `net8.0` (requis par le kernel pinné), il faut soit retargeter temporairement le `.csproj` en `net8.0` puis `dotnet build`, soit — solution propre — multi-targeter le fork en `<TargetFrameworks>net8.0;net9.0</TargetFrameworks>` (follow-up sur le fork, `Extensions`/SkiaSharp restant net9.0-only). Les bins référencés par MGS-1..5 doivent exister sous `src/MetaGeneticSharp.Domain/bin/Debug/net8.0/`.

Les notebooks chargent les DLL via `#r "c:/dev/MetaGeneticSharp/..."` (chemin du checkout de travail du fork). **MGS-1..5** pointent sur `src/MetaGeneticSharp.Domain/bin/Debug/net8.0/` (4 DLL : GeneticSharp.Domain, GeneticSharp.Infrastructure.Framework, MetaGeneticSharp.Domain, MetaGeneticSharp.Infrastructure) ; **MGS-6..12** pointent sur `src/MetaGeneticSharp.Extensions/bin/Debug/net9.0/` (Extensions + SkiaSharp + System.Drawing.Common). Les résultats numériques des notebooks MGS-1 à MGS-9 sont **stochastiques** (le RNG du framework n'y est pas seedé) : les outputs committés sont une exécution valide, les valeurs varient d'une exécution à l'autre. **MGS-10** fait exception : le banc y est **seedé** (`FastRandomRandomization.ResetSeed(masterSeed)` ancre le RNG global une fois avant la suite), de sorte que les chiffres de la table de biais central sont **reproduisibles** d'une exécution à l'autre. **MGS-11** aussi : il appelle `FastRandomRandomization.ResetSeed(42)` avant chaque banc, son verdict est **reproductible** (caveat : graine unique, pas un banc multi-graines). **MGS-12** de même : il reseed le RNG avant chaque paire optimiseur (rotationné vs non), de sorte que les deltas committés sont reproductibles (caveat : dimension 2 et budget large → $\Delta \approx 0$ pour tous ; révéler l'effet *opérateur* demande une dimension plus élevée, cf exercice 2).

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
| MGS-10 (CenterBias) | Differential Evolution | Storn, R., & Price, K. (1997) — « Differential Evolution – A Simple and Efficient Heuristic for Global Optimization over Continuous Spaces », *Journal of Global Optimization* 11. |
| MGS-10 (CenterBias) | Bare-Bones Particle Swarm | Kennedy, J. (2003) — « Bare Bones Particle Swarms », *Proc. IEEE Swarm Intelligence Symposium*. |
| MGS-10 (CenterBias) | Recuit simulé (Simulated Annealing) | Metropolis, N., Rosenbluth, A. W., Rosenbluth, M. N., Teller, A. H., & Teller, E. (1953) — « Equation of State Calculations by Fast Computing Machines », *Journal of Chemical Physics* 21(6) ; Kirkpatrick, S., Gelatt, C. D., & Vecchi, M. P. (1983) — « Optimization by Simulated Annealing », *Science* 220(4598). |
| MGS-10 (CenterBias) | Test du biais central (centré-vs-déplacé) | Kudela, H. (2022) — protocole centré-vs-déplacé (centered-vs-shifted). |
| MGS-11 (IslandSynergy) | Modèle insulaire, synergie d'îles hétérogènes | Sørensen, K. (2015) — « Metaheuristics—the metaphor exposed », *Intl. Trans. in Operational Research* 22(1). doi:10.1111/itor.12001 |
| MGS-9 (EverestRelief) | Particle Swarm Optimization (baseline) | Kennedy, J., & Eberhart, R. (1995) — « Particle Swarm Optimization », *Proc. IEEE Int. Conf. on Neural Networks*. |
| MGS-6, MGS-7 | No-Free-Lunch | Wolpert, D. H., & Macready, W. G. (1997) — « No free lunch theorems for optimization », *IEEE Trans. on Evolutionary Computation* 1(1). |

---

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Cette quatrième partie a changé la question : non plus *« quelle métaheuristique choisir »* (Parties 1-2), mais *« comment construire et combiner des métaheuristiques à partir de primitives »*. L'arc pédagogique, porté par onze notebooks C# .NET 9 au-dessus de [MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp), démontre la thèse **composants > métaphores** :

- **Le moteur autonome** (MGS-1, MGS-2) — un `MetaGeneticAlgorithm` qui pilote l'évolution sans dépendre de la classe `GeneticAlgorithm` amont, et la grammaire fluente (`Match`, `Container`, `Scoped`) qui permet d'assembler une métaheuristique en quelques lignes déclaratives lisibles. C'est le socle : tout le reste compose au-dessus.
- **La structuration de population** (MGS-3, MGS-4) — le modèle eucaryote (sous-populations spécialisées portées par des chromosomes composites) et le modèle insulaire (îles migratoires) : deux configurations qu'aucune bibliothèque monolithique grand public n'offre directement, et qui deviennent naturelles une fois la composition maîtrisée.
- **La reconstruction des composés publiés** (MGS-5) — WOA, EO, FBI : pour chaque algorithme du catalogue, le parcours en trois temps (description → reconstruction depuis les primitives `BuildMainHeuristic()` → raccourci factory prouvant l'équivalence). C'est l'argument poussé jusqu'à la **preuve** : reconstruire un algorithme bio-inspiré *démontre* son mécanisme au lieu de le cacher derrière une métaphore animale (critique de Sørensen, 2015).
- **La confrontation honnête** (MGS-6) — dix fonctions benchmark standard, comparaison Uniform / WOA / Islands sans trier les victoires : WOA gagne ou égalise sur 7/10 mais **diverge sur Schwefel**, démonstration de No-Free-Lunch là où `mealpy` masquerait le mécanisme.
- **L'agnosticisme à la représentation** (MGS-7) — la même `IslandMetaHeuristic` appliquée à un TSP-20 (permutation) sans aucune adaptation : la grammaire vit *sous* la couche géométrique et ne lit jamais `Gene.Value`. Le transfert continu → combinatoire sans réécriture.
- **La visualisation des paysages** (MGS-8, MGS-9) — de vraies heatmaps PNG (fonction analytique, carte d'altitude, relief terrestre réel Everest) qui rendent le choix d'une métaheuristique *éclairé* plutôt que *doctrinal*, et un flipbook de convergence montrant la population se contracter vers le sommet.
- **La caractérisation du biais central** (MGS-10) — le protocole centré-vs-déplacé (Kudela 2022) confronte huit optimiseurs (Random, GA, WOA, EO, FBI, DE, BBPSO, Recuit simulé) sur un banc **seedé** (chiffres reproduisibles). Lecture fonction par fonction : sur Sphere (trop facile) et Rastrigin (trop bruitée à NFE = 5000) le signal n'est pas fiable, mais sur **Ackley** — la fonction conçue pour exposer le biais — **seul WOA** présente un biais central ($\Delta = +4,36$ : il résout le cas centré mais rate le cas déplacé) ; les sept autres, y compris les composés « métaphoriques » EO, FBI, BBPSO, sont **robustes**. Leçon affûtée de « composants > métaphores » : ce n'est pas l'étiquette métaphorique qui prédit le biais — EO, FBI, BBPSO sont eux aussi métaphoriques mais robustes — c'est la **structure de l'opérateur** : l'encerclement de la meilleure position (WOA) ancre vers le centre, là où l'arithmétique libre (DE, Recuit simulé) ou le pool d'équilibre (EO) n'y ancrent pas. Une **seconde preuve**, plus fine, au-delà de la performance brute (MGS-6).
- **La mesure d'une synergie** (MGS-11) — la composition est-elle magique ? Un archipel hétérogène (îles DE exploratrices + îles BBPSO exploitantes) est confronté, à budget égal sur fonctions dé-biaisées en dim 5, à ses constituants homogènes. Verdict **négatif** (0/2 synergie) : la migration entre opérateurs dissemblables peut *propager les solutions piégées* et produire un compromis *inférieur* au meilleur constituant. La synergie d'îles n'est pas automatique — elle se **démontre**, ne se décrète pas : « composants > métaphores » poussée jusqu'à la *mesure falsifiable* de la composition.

Le véritable enseignement rejoint celui des Parties 1-2 : aucune métaheuristique ne domine partout, et la bonne réponse à un problème d'optimisation est rarement « l'algorithme X » mais plutôt « **la bonne composition de primitives pour ce paysage de fitness** ».

### Prochaines étapes

- **Le code source de la bibliothèque** : le [fork jsboige/MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) — code source, tests unitaires, et feuille de route ([ROADMAP.md](https://github.com/jsboige/MetaGeneticSharp/blob/main/ROADMAP.md)) — prolonge cette partie vers une vraie bibliothèque industrialisable. Les notebooks ne sont que la vitrine pédagogique des briques qui y vivent.
- **Retour aux fondamentaux Python** : après avoir reconstruit WOA et EO à la main, reprendre [Search-11-Metaheuristics](../Part1-Foundations/Search-11-Metaheuristics.ipynb) (PSO, ABC, SA, BRO via `mealpy`) — l'appel de fonction y apparaît alors comme un *raccourci* au-dessus des mécanismes qu'on vient de reconstruire, et l'on mesure ce que la composition déclarative apporte.
- **Le pont vers l'ingénierie** : les patterns de composition (sous-populations spécialisées, migration, hybrides assemblés par grammaire fluente) existent dans la littérature mais sont rares dans les libs grand public — cette partie est le socle pour les implémenter en production sur un runtime .NET typé.
- **La série dans son ensemble** : le [sommaire Search](../README.md) cartographie les quatre parties — celle-ci est le side track C# .NET qui démontre que les concepts Python (Search-5 génétique, Search-11 métaheuristiques) se retrouvent, solidement typés et composables, dans un vrai moteur.

### Le fil rouge

Les métaheuristiques composables proposent un changement de regard sur l'optimisation : ne plus voir un algorithme bio-inspiré comme une **boîte noire** qu'on invoque (et dont on ignore le mécanisme caché derrière une métaphore animale), mais comme une **composition de primitives** qu'on peut intercepter, lire et recomposer. Reconstruire WOA ou Equilibrium Optimizer à partir de `Match`, `IfElse` et de croisements géométriques, c'est *démontrer* leur mécanisme plutôt que le postuler ; les confronter sur des benchmarks sans trier les victoires (divergence sur Schwefel), c'est éprouver le No-Free-Lunch au lieu de le réciter ; appliquer la même grammaire à un TSP combinatoire puis à un relief terrestre réel, c'est prouver l'agnosticisme de la représentation. La leçon transversale : la puissance d'une métaheuristique ne réside pas dans sa métaphore (baleine, équilibre, essaim) mais dans les **briques réutilisables** qu'elle assemble — et les composer soi-même est précisément ce qui transforme un utilisateur de bibliothèque en praticien capable d'inventer la configuration adaptée à un paysage de fitness donné.

## Liens

- [Fork jsboige/MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) — code source, tests, ROADMAP
- [GeneticSharp PR #87](https://github.com/giacomelli/GeneticSharp/pull/87) — origine du projet (couche métaheuristiques 2020-2022)
- [Search-11-Metaheuristics](../Part1-Foundations/Search-11-Metaheuristics.ipynb) — introduction Python (PSO, ABC, SA, BRO) et benchmarks comparatifs
- [Série Search](../README.md) — vue d'ensemble

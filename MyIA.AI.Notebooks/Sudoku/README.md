---
pagetitle: "Sudoku — comparer les méthodes de résolution"
---

# Sudoku — comparer les méthodes de résolution

<!-- CATALOG-STATUS
series: Sudoku
pedagogical_count: 39
breakdown: root=39
maturity: BETA=38, ALPHA=1
-->

[↑ Parcours de notebooks](../README.md) · [Search : recherche et contraintes](../Search/README.md)

Comment résoudre la même grille par des méthodes aussi différentes que le retour arrière, la programmation par contraintes et un réseau de neurones ? Le Sudoku offre un problème commun pour étudier ce que chaque représentation rend possible : explorer des candidats, propager une déduction, déclarer les règles à un solveur ou apprendre à prédire les cases.

Cette série s'adresse aux étudiants en informatique et aux enseignants cherchant un fil conducteur pour comparer les paradigmes de l'IA. Les bases de Python ou de C# suffisent pour commencer ; les notions de recherche et de contraintes sont introduites dans les premiers paliers. Les approches probabilistes, neuronales et formelles demandent ensuite les prérequis indiqués ci-dessous. Les variantes C# et Python permettent de choisir son langage ; elles présentent le même problème pédagogique avec des bibliothèques et parfois des expériences différentes.

Vous apprendrez à implémenter un solveur, à modéliser ses contraintes, à distinguer une solution valide d'une prédiction plausible et à concevoir une comparaison expérimentale. Le Sudoku généralisé est NP-complet ; les grilles de taille fixée du cours permettent d'en examiner concrètement les stratégies, sans déduire leur difficulté de leur seul nombre d'indices.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue parcours, approfondissements et recherche.

- **Vous découvrez** : commencez par 01, ou par 00 pour le socle C#. La table principale suit les numéros nus ; chaque paire de langages partage une ligne.
- **Vous creusez un palier** : 12b étudie l'interface LINQ de Z3 ; 18b développe la méthode statistique du benchmark.
- **Vous cherchez des prolongements** : les résultats neuronaux, l'audit des corpus et les preuves de propagation se trouvent dans « Pour aller plus loin ».

Les premiers paliers conduisent de l'exploration exacte aux recherches approchées. Les contraintes ramènent ensuite la question à la représentation des règles ; les modèles appris posent celle de la généralisation. La comparaison expérimentale et la formalisation donnent enfin des moyens différents de justifier une conclusion.

```mermaid
flowchart LR
    A["Retour arrière et couverture exacte"] --> B["Métaheuristiques"]
    B --> C["Propagation et solveurs de contraintes"]
    C --> D["Représentations symboliques"]
    D --> E["Inférence et apprentissage"]
    E --> F["Comparer, prouver, auditer"]
```

## Parcours principal — Découverte, Licence et lectures avancées

Le public indiqué reprend la profondeur des contenus : les preuves du palier 19 et la méthodologie du 20 demandent une lecture avancée. Les bases de récursion de 01 préparent 02 et 06 ; les contraintes de 06–07 préparent les solveurs et la preuve de propagation. Les paliers 15–16 supposent probabilités et apprentissage, 19 une initiation à Lean.

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 00 | Environment — [C#](Sudoku-00-Environment-CSharp.ipynb) | Préparer les grilles, interfaces de solveur et outils de mesure utilisés dans les carnets C#. | Découverte | — |
| 01 | Backtracking — [C#](Sudoku-01-Backtracking-CSharp.ipynb) · [Python](Sudoku-01-Backtracking-Python.ipynb) | Explorer une grille par retour arrière ; relier ordre des choix, validité et coût de recherche. | Découverte | — |
| 02 | Dancing Links — [C#](Sudoku-02-DancingLinks-CSharp.ipynb) · [Python](Sudoku-02-DancingLinks-Python.ipynb) | Traduire le Sudoku en couverture exacte et organiser la recherche avec les Dancing Links de Knuth. | Découverte | — |
| 03 | Genetic — [C#](Sudoku-03-Genetic-CSharp.ipynb) · [Python](Sudoku-03-Genetic-Python.ipynb) | Faire évoluer une population de grilles ; comparer les effets du codage, du croisement et de la mutation. | Découverte | — |
| 04 | Simulated Annealing — [C#](Sudoku-04-SimulatedAnnealing-CSharp.ipynb) · [Python](Sudoku-04-SimulatedAnnealing-Python.ipynb) | Explorer un paysage de conflits par recuit simulé : voisinage, température et acceptation de dégradations. | Découverte | — |
| 05 | PSO — [C#](Sudoku-05-PSO-CSharp.ipynb) · [Python](Sudoku-05-PSO-Python.ipynb) | Adapter l'essaim de particules à un problème discret et étudier ses paramètres. | Découverte | — |
| 06 | AIMA CSP — [C#](Sudoku-06-AIMA-CSP-CSharp.ipynb) · [Python](Sudoku-06-AIMA-CSP-Python.ipynb) | Définir variables, domaines et contraintes ; combiner choix de variable, propagation et retour arrière. | Licence | — |
| 07 | Norvig — [C#](Sudoku-07-Norvig-CSharp.ipynb) · [Python](Sudoku-07-Norvig-Python.ipynb) | Construire la propagation de Norvig par élimination des candidats, puis rechercher lorsque les déductions ne suffisent plus. | Licence | — |
| 08 | Human Stratégies — [C#](Sudoku-08-HumanStrategies-CSharp.ipynb) · [Python](Sudoku-08-HumanStrategies-Python.ipynb) | Exprimer des stratégies humaines sur les candidats : singles, paires et interactions entre lignes, colonnes et blocs. | Licence | — |
| 09 | Graph Coloring — [C#](Sudoku-09-GraphColoring-CSharp.ipynb) · [Python](Sudoku-09-GraphColoring-Python.ipynb) | Représenter les conflits entre cases par un graphe et résoudre une coloration sous contraintes. | Licence | — |
| 10 | OR-Tools — [C#](Sudoku-10-ORTools-CSharp.ipynb) · [Python](Sudoku-10-ORTools-Python.ipynb) | Modéliser avec OR-Tools ; passer de la satisfaction des règles à l'optimisation d'un carré latin pondéré. | Licence | — |
| 11 | Choco — [C#](Sudoku-11-Choco-CSharp.ipynb) · [Python](Sudoku-11-Choco-Python.ipynb) | Utiliser les contraintes et propagateurs de Choco depuis C# avec IKVM ou depuis Python avec JPype. | Licence | — |
| 12 | Z3 SMT — [C#](Sudoku-12-Z3-CSharp.ipynb) · [Python](Sudoku-12-Z3-Python.ipynb) | Exprimer les contraintes avec Z3, combiner arithmétique et logique, puis utiliser une fonction objectif. | Licence | [12b](#autour-de-12--une-interface-linq-licence). |
| 13 | Symbolic Automata — [C#](Sudoku-13-SymbolicAutomata-CSharp.ipynb) · [Python](Sudoku-13-SymbolicAutomata-Python.ipynb) | Distinguer reconnaissance d'une grille remplie et recherche d'une solution avec expressions régulières, automates et Z3. | Licence | — |
| 14 | BDD/MDD — [C#](Sudoku-14-BDD-CSharp.ipynb) · [Python](Sudoku-14-BDD-Python.ipynb) | Construire des diagrammes de décision binaires et multi-valués pour représenter des contraintes symboliquement. | Licence | — |
| 15 | Infer ↔ NumPyro — [C#](Sudoku-15-Infer-CSharp.ipynb) · [Python](Sudoku-15-Infer-Python.ipynb) | Modéliser une distribution sur les cases avec Infer.NET en C# ou NumPyro/JAX en Python ; examiner sa relation à la validité. | Licence | — |
| 16 | Neural Network — [Python](Sudoku-16-NeuralNetwork-Python.ipynb) | Comparer réseaux directs et itératifs ; distinguer précision par case et résolution complète d'une grille. | Licence | — |
| 17 | LLM — [Python](Sudoku-17-LLM-Python.ipynb) | Comparer résolution par prompt et utilisation de code ; vérifier les grilles produites par un modèle de langage. | Licence | — |
| 18 | Comparison — [C#](Sudoku-18-Comparison-CSharp.ipynb) · [Python](Sudoku-18-Comparison-Python.ipynb) | Construire un protocole comparatif de solveurs et interpréter temps, succès et coût de recherche. | Licence | [18b](#autour-de-18--comparer-statistiquement-recherche). |
| 19 | Lean Propagation — [Lean](Sudoku-19-Lean-Propagation-Lean.ipynb) | Lire des preuves Lean de correction de la propagation : une élimination justifiée conserve les solutions possibles. | Recherche | — |
| 20 | Corpus Audit — [Python](Sudoku-20-CorpusAudit-Python.ipynb) | Auditer un corpus de puzzles : validité, unicité, propagation seule, effort de recherche et indices redondants. | Recherche | — |

## Approfondissements — Licence et Recherche

### Autour de 12 — une interface LINQ (Licence)

[12b — Z3.Linq](Sudoku-12b-Z3-Linq2Z3-CSharp.ipynb) reprend la modélisation de 12 côté C# avec une interface déclarative : propriétés, collections et tableaux. Il permet de comparer l'expressivité du langage d'accès à Z3 avec l'API native, sur les exemples du carnet. Prérequis supplémentaires : C#, LINQ et lecture des contraintes de 12.

### Autour de 18 — comparer statistiquement (Recherche)

[18b — Comparaison statistique](Sudoku-18b-Statistical-Comparison-Python.ipynb) distingue bruit de chronométrage et variation entre puzzles. Il utilise médianes par puzzle, intervalles bootstrap, test apparié de Wilcoxon, taille d'effet et correction de comparaisons multiples. Prérequis : protocole de 18 et statistiques inférentielles élémentaires. Dans le banc facile affiché, le retour arrière naïf est plus rapide que MRV : le coût d'une heuristique peut dépasser son bénéfice sur les instances choisies.

## Ce que les représentations permettent — Licence

### Explorer ou propager

Le retour arrière complète progressivement une grille et revient sur une décision lorsqu'elle conduit à une impasse. L'ordre des choix affecte le travail effectué. La couverture exacte de 02 reformule les règles en contraintes sur les affectations possibles ; Dancing Links permet de retirer puis restaurer efficacement les éléments explorés.

[![Grille résolue par retour arrière, avec distinction des indices et des valeurs trouvées](assets/readme/sudoku1-backtracking.png)](Sudoku-01-Backtracking-Python.ipynb)

La propagation de 06–08 exploite les conséquences des décisions avant de poursuivre la recherche. MRV choisit une case parmi les plus contraintes ; les déductions sur les candidats peuvent résoudre certaines cases sans branchement. Les mêmes idées se retrouvent dans les solveurs déclaratifs de 10–12 : le modèle pose les règles, le solveur organise propagation et recherche. Un modèle incomplet peut accepter de mauvaises grilles ; un modèle trop contraint peut exclure des solutions.

[![Grille résolue par le modèle de contraintes Choco](assets/readme/sudoku11-choco.png)](Sudoku-11-Choco-Python.ipynb)

### Changer l'encodage d'une recherche approchée

Les métaheuristiques de 03–05 cherchent à réduire les conflits sans garantie de trouver une solution. La représentation des candidats modifie le paysage exploré. La figure de 03 compare un génome par cases à un génome par permutations de blocs : préserver les contraintes de bloc dès l'encodage change la convergence observée. Ce résultat appartient à l'expérience affichée ; les autres essais du carnet montrent aussi des échecs.

[![Évolution des conflits pour deux représentations génétiques, par cases et par permutations](assets/readme/sudoku3-genetic.png)](Sudoku-03-Genetic-Python.ipynb)

Le recuit ajoute une température qui permet d'accepter temporairement une dégradation ; le PSO demande d'adapter ses déplacements au problème discret. Les exercices font varier encodage, voisinage et paramètres pour observer leurs effets, plutôt que supposer qu'une méthode domine sur toute grille.

### Vérifier, résoudre et optimiser

En 13, reconnaître une grille remplie et chercher les valeurs qui manquent sont deux opérations distinctes : les expressions régulières ou automates assurent certaines vérifications, Z3 prend en charge la recherche dans les expériences correspondantes. Les diagrammes de décision de 14 étudient une autre représentation des contraintes ; leur compacité dépend de la formule et de l'ordre des variables.

Les paliers 10 et 12 ajoutent un objectif aux contraintes. Sur leur même instance Python de carré latin pondéré, CP-SAT et Z3 obtiennent une récompense maximale de **178**. Le carnet 10 trouve aussi **73** pour son problème de minimisation. La variante C# de 12 obtient **192** sur une autre instance : ce n'est pas une divergence entre moteurs sur un problème identique. Une solution faisable satisfait les règles ; établir son optimalité demande en plus de justifier qu'aucune meilleure valeur de l'objectif n'est possible.

### Prédire une case ou résoudre une grille

L'inférence probabiliste de 15 attribue des distributions aux cases. Le réseau de 16 apprend des prédictions à partir de données. Dans les deux cas, une confiance élevée pour chaque case ne garantit pas que leur combinaison respecte toutes les règles. La courbe du MLP rend cette distinction visible : la précision par case progresse, tandis que la précision par grille reste très faible.

[![Perte et précision du MLP pendant l'entraînement, mesurées par case et par grille](assets/readme/sudoku16-nn-training.png)](Sudoku-16-NeuralNetwork-Python.ipynb)

La carte des erreurs du CNN itératif montre où les erreurs se répartissent sur le jeu évalué. Elle compte des erreurs par position ; sans rapporter ces comptes au nombre de cases à prédire, elle ne mesure pas à elle seule une difficulté intrinsèque de chaque position.

[![Comptes d'erreurs par position de la grille pour le CNN itératif](assets/readme/sudoku16-nn-errors.png)](Sudoku-16-NeuralNetwork-Python.ipynb)

En 17, la comparaison porte sur le rôle du modèle de langage : proposer directement des chiffres ou produire du code qui les recherche. La sortie conservée porte sur **deux puzzles** : zéro réussite pour les prompts directs et avec exemples, deux réussites avec l'approche utilisant du code. Ce petit banc illustre un protocole et ne donne pas un taux général de réussite des LLM.

## Installation — pratique, tous niveaux

Commencer par le carnet de la méthode choisie dans un clone du dépôt, qui fournit les puzzles, les bibliothèques locales et les ressources voisines.

| Parcours | Préparation |
|---|---|
| Python | Python 3.10 ou ultérieur ; environnement dédié et dépendances de [requirements.txt](requirements.txt). Les expériences classiques utilisent le CPU. |
| C# | SDK .NET 9 et noyau .NET Interactive. Le carnet [00](Sudoku-00-Environment-CSharp.ipynb) définit le socle importé par les suivants ; les directives NuGet installent leurs bibliothèques. |
| Choco en Python | JVM accessible et `jpype1` ; le carnet 11 télécharge le JAR Choco. |
| Choco en C# | Runtime IKVM et DLL Choco partagée sous [Search/Part2-CSP](../Search/Part2-CSP/). Suivre la cellule de préparation de 11. |
| Inférence probabiliste | Infer.NET pour 15 C# ; JAX et NumPyro pour 15 Python. |
| Réseaux | PyTorch pour 16 ; le GPU accélère les entraînements, tandis que les démonstrations CPU et la lecture des résultats restent accessibles. |
| Modèle de langage | Pour rejouer 17, service compatible avec l'API utilisée, endpoint et identifiants configurés dans l'environnement. |
| Lean | Pour 19, noyau Lean et projet [sudoku_lean](sudoku_lean/) construit avec sa toolchain. |

Le paquet Python de Z3 est `z3-solver`. Les approches symboliques utilisent aussi `regex` et `dd` ; 17 utilise `python-dotenv` pour la configuration ; ce paquet doit être ajouté à l’environnement car il est absent du manifeste commun. En cas d'import manquant, vérifier que Jupyter emploie bien l'environnement où les paquets ont été installés. Côté C#, contrôler la présence du noyau avec `jupyter kernelspec list` et les imports du carnet 00.

## Pour aller plus loin — Recherche

### Comparer des solveurs et auditer les puzzles

Les temps dépendent du solveur, de ses paramètres, de la machine et surtout des instances. [18](Sudoku-18-Comparison-Python.ipynb) construit la comparaison ; [18b](Sudoku-18b-Statistical-Comparison-Python.ipynb) en examine la variabilité. Pour ajouter une méthode, conserver les puzzles et le protocole, puis vérifier les solutions produites avant de comparer les temps.

[20 — Audit des corpus](Sudoku-20-CorpusAudit-Python.ipynb) examine les fichiers de [Puzzles](Puzzles/). Les sorties distinguent les grilles résolues par propagation seule de celles qui demandent une recherche, testent l'unicité par dénombrement plafonné et repèrent les indices redondants. Sur les corpus du carnet, `top95` demande davantage de recherche que `Easy51`, alors que le nom « hardest » ne suffit pas à prédire ce classement. Le nombre d'indices ne constitue donc pas une échelle de difficulté indépendante du solveur.

### Réseaux relationnels récurrents

Le réseau relationnel récurrent (RRN) de Palm et ses coauteurs propage des messages sur le graphe de contraintes. Le carnet [16](Sudoku-16-NeuralNetwork-Python.ipynb) compare cette approche aux réseaux directs et à des procédures itératives.

Ses sorties archivent une précision par grille d'environ **33,5 %** pour les architectures du banc initial, puis **83,5 %** après un entraînement complémentaire sur davantage de données. Elles montrent l'intérêt d'examiner les données et le protocole, au-delà du seul nombre de paramètres. Ces expériences changent plusieurs conditions ; elles n'isolent pas à elles seules l'effet causal du volume de données ou du curriculum. Les fichiers JSON d'entraînement lus pour produire cette synthèse sont absents du dépôt : la sortie conservée documente ces expériences, mais ne suffit pas à les régénérer.

Un taux élevé reste une mesure sur un jeu d'évaluation. Pour une application exigeant une grille valide, contrôler les contraintes demeure nécessaire après une prédiction neuronale.

### Formalisations Lean

[19 — Propagation en Lean](Sudoku-19-Lean-Propagation-Lean.ipynb) étudie la correction des déductions de type *naked single* et *hidden single*, notamment via `peer_excludes_value`. Le projet [sudoku_lean](sudoku_lean/) fournit les définitions et preuves : on examine ce que les hypothèses permettent de conclure, ainsi que les dépendances affichées par `#print axioms`. La correction d'une règle de propagation ne constitue pas une preuve de complétude d'un solveur entier.

L'inventaire des modules et des toolchains figure dans [LEAN_INVENTORY.md](LEAN_INVENTORY.md).

### Prolonger le problème commun

- La propagation de 06–07 ouvre sur [Search/Part2-CSP](../Search/Part2-CSP/README.md), où variables, domaines et contraintes s'appliquent à d'autres problèmes.
- L'encodage Z3 de 12 prépare la [série SMT](../SymbolicAI/SMT/README.md), qui utilise la satisfiabilité pour explorer et vérifier d'autres modèles.
- Le palier 15 donne un point de départ vers [Probas/Infer](../Probas/Infer/README.md) pour approfondir la modélisation et l'inférence probabilistes.

Une application possible est de reprendre le benchmark 18 avec un solveur hybride : utiliser un réseau pour proposer un ordre de variables, puis une recherche sous contraintes pour contrôler les solutions.

## Ressources — tous niveaux

### Livres, articles et figures

- [Peter Norvig — Solving Every Sudoku Puzzle](http://norvig.com/sudoku.html).
- [Donald Knuth — Dancing Links](https://arxiv.org/abs/cs/0011047).
- [Russell et Norvig — Artificial Intelligence: A Modern Approach](https://aima.cs.berkeley.edu/), chapitres de recherche et de contraintes.
- Les figures ci-dessus sont liées à leur carnet source ; le [manifeste des figures](assets/readme/MANIFEST.md) en consigne la provenance.

### Bibliothèques

[OR-Tools](https://developers.google.com/optimization) · [Z3](https://z3prover.github.io/api/html/namespacez3py.html) · [NetworkX](https://networkx.org/) · [GeneticSharp](https://github.com/giacomelli/GeneticSharp) · [Choco](https://choco-solver.org/) · [Infer.NET](https://dotnet.github.io/infer/) · [PyTorch](https://pytorch.org/) · [client Python OpenAI](https://github.com/openai/openai-python).

### Provenance pédagogique

Les carnets reprennent notamment des projets étudiants consacrés à Norvig et sa variante BitArray (`Sudoku.Norvig`, `Sudoku.NorvigBitArray`), au recuit (`Sudoku.SimulatedAnnealing`), aux stratégies humaines (`Sudoku.Human`), aux réseaux (`Sudoku.NeuralNetwork`), au PSO (`Sudoku.PSO`), aux CSP (`Sudoku.CspAima`), à la coloration (`Sudoku.GraphColoring`), à Choco (`Sudoku.ChocoSolvers`) et aux LLM (`Sudoku.LLM-ChatGPTenzin`). Les carnets explicitent les adaptations et les outils utilisés.

[Retour aux notebooks](../README.md) · [Catalogue du dépôt](../../COURSE_CATALOG.generated.md) · [Licence](../../LICENSE)

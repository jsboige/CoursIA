# Planification automatique — décider quoi faire

[← Lean](../Lean/README.md) | [↑ SymbolicAI](../README.md) | [SmartContracts →](../SmartContracts/README.md)

<!-- CATALOG-STATUS
series: SymbolicAI-Planners
pedagogical_count: 26
breakdown: Planners=26
maturity: BETA=26
-->

La planification automatique répond à une question différente de celle de l'apprentissage : non pas « que prédire ? » mais « **que faire ?** ». À partir d'un modèle du monde — un état initial, des actions avec leurs préconditions et leurs effets, un but — un planificateur cherche une suite d'actions qui mène au but. C'est une technologie éprouvée : elle pilote des robots, ordonnance la logistique et a dirigé des engins spatiaux autonomes.

La série part du modèle STRIPS et du langage PDDL, puis descend l'arc des paradigmes : recherche heuristique avec Fast Downward, contraintes avec CP-SAT, temps avec PDDL 2.1, hiérarchie avec les réseaux de tâches, et enfin la frontière neuro-symbolique, où un modèle de langage ou une politique apprise remplacent la règle écrite à la main.

**À qui elle s'adresse.** Un lecteur qui sait programmer — Python, ou C# pour les jumeaux — et qui n'a jamais fait de planification. Les carnets introduisent le vocabulaire depuis zéro ; le carnet de mise en route installe l'environnement avant le premier concept.

## Aperçu en images — découverte

Les figures ci-dessous sont extraites des sorties réelles des carnets, une par concept. Leur provenance exacte — cellule, sortie, poids, texte alternatif — est tenue dans [`assets/readme/MANIFEST.md`](assets/readme/MANIFEST.md).

<p align="center"><a href="01-Foundation/Planners-03-State-Space-Python.ipynb"><img src="assets/readme/planners3-statespace.png" width="540" alt="Espace d'états : explosion combinatoire de la recherche aveugle dans un graphe d'états PDDL, motivant le recours aux heuristiques."></a></p>

<p align="center"><a href="02-Classical/Planners-05-Heuristics-Python.ipynb"><img src="assets/readme/planners5-heuristics.png" width="540" alt="Heuristiques de recherche : comparaison de A* et de ses variantes guidant l'exploration vers le but."></a></p>

<p align="center"><a href="03-Advanced/Planners-07-OR-Tools-Python.ipynb"><img src="assets/readme/planners7-ortools.png" width="540" alt="OR-Tools CP-SAT : diagramme de Gantt d'un ordonnancement job-shop produit par le solveur."></a></p>

<p align="center"><a href="03-Advanced/Planners-08-Temporal-Python.ipynb"><img src="assets/readme/planners8-temporal.png" width="560" alt="Planification temporelle : chronologie d'actions avec durées et contraintes de scheduling sur un réseau temporel."></a></p>

## Comment lire ce README — découverte

Le parcours suit le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : les numéros nus donnent la progression, les lettres approfondissent un palier.

- **Vous découvrez** : suivez la table du parcours principal, de haut en bas. Les jumeaux Python et C# d'un même numéro partagent une ligne.
- **Vous creusez un palier** : ouvrez l'approfondissement correspondant — 5b et 5c autour de 05, 10b autour de 10. Chacun dit ce qu'il ajoute et le prérequis qu'il suppose en plus.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » porte les formalisations Lean, les mesures qui restent ouvertes et les ponts avec les autres séries.

## Parcours principal — lecture guidée et prérequis

Chaque numéro introduit un concept et ne suppose que ce qui le précède ; lu de haut en bas, il donne le parcours complet de la série. Un jumeau C# se lit seul : sa première tranche est écrite en C# pur, sans service ni Python.

| # | Notebook | Ce qu'on y apprend | Public et prérequis | Pour approfondir |
|---|---|---|---|---|
| 00 | [Planners-00-Setup](00-Environment/Planners-00-Setup-Python.ipynb) | Vérifier l'environnement avant tout : `unified-planning`, OR-Tools, disponibilité de Fast Downward par le service ou par le plugin local, puis un premier domaine PDDL exécuté | Aucun prérequis de planification ; Python 3.9+ | À exécuter une fois, puis ouvrir 01 |
| 01 | [Planners-01-Introduction-Python](01-Foundation/Planners-01-Introduction-Python.ipynb) · [C#](01-Foundation/Planners-01-Introduction-Csharp.ipynb) | Le triptyque État-Action-But, les hypothèses de STRIPS — statique, déterministe, observable, discret, instantané — et la taxonomie des paradigmes. Le jumeau C# refait l'introduction en C# pur, puis branche un moteur de production | Aucun | 02 |
| 02 | [Planners-02-PDDL-Basics-Python](01-Foundation/Planners-02-PDDL-Basics-Python.ipynb) · [C#](01-Foundation/Planners-02-PDDL-Basics-Csharp.ipynb) | Syntaxe PDDL : domaines, problèmes, types, prédicats, actions, préconditions, effets. Le jumeau C# implémente un STRIPS complet — modèle typé, grounding, BFS forward — sur Logistics et Gripper | Après 01 ; logique propositionnelle | 03 |
| 03 | [Planners-03-State-Space-Python](01-Foundation/Planners-03-State-Space-Python.ipynb) · [C#](01-Foundation/Planners-03-State-Space-Csharp.ipynb) | Représenter l'espace d'états et mesurer son explosion combinatoire en $O(2^n)$ : pourquoi la recherche aveugle ne suffit pas. Le jumeau C# oppose BFS, DFS, Greedy et A* sur un terrain uniforme puis pondéré, avec QuikGraph puis Fast Downward | Après 02 ; graphes et parcours | [Partie 2](02-Classical/README.md) : les heuristiques |
| 04 | [Planners-04-Fast-Downward-Python](02-Classical/Planners-04-Fast-Downward-Python.ipynb) · [C#](02-Classical/Planners-04-Fast-Downward-Csharp.ipynb) | L'architecture en trois étages de Fast Downward — traduction PDDL vers SAS+, prétraitement, recherche — et A*, GBFS, EHC sur Blocks World et Logistics. Le jumeau C# écrit un planificateur SAS+ complet (prevail/pre/eff, h^max et h^FF par RPG) sur Ferry et Logistics | Après 03 ; A* | 05 |
| 05 | [Planners-05-Heuristics-Python](02-Classical/Planners-05-Heuristics-Python.ipynb) · [C#](02-Classical/Planners-05-Heuristics-Csharp.ipynb) | Classification admissible ou non — h^add, h^max, h^FF, LM-cut — et comparaison expérimentale du nombre de nœuds expansés. Le jumeau C# dérive ces heuristiques et les landmarks, démontre la non-admissibilité de h^add et valide h\* = 4 sur Blocks World | Après 04 ; notion d'optimalité | [Paliers 5b et 5c](#autour-de-05--prouver-ladmissibilité-mesurer-une-primitive) |
| 06 | [Planners-06-Domains-Python](02-Classical/Planners-06-Domains-Python.ipynb) · [C#](02-Classical/Planners-06-Domains-Csharp.ipynb) | Les domaines standards de l'IPC — Blocks World, Logistics, Gripper, Ferry, Hanoï — par complexité croissante. Le jumeau C# modélise atomes, actions et états, avec un BFS forward et anti-cycle | Après 05 | [Partie 3](03-Advanced/README.md) : changer de paradigme |
| 07 | [Planners-07-OR-Tools-Python](03-Advanced/Planners-07-OR-Tools-Python.ipynb) · [C#](03-Advanced/Planners-07-OR-Tools-Csharp.ipynb) | Programmation par contraintes avec CP-SAT : all-different, cumulative, table, ordonnancement, optimisation multi-objectif. Le jumeau C# écrit d'abord un solveur CP à propagation et backtracking sur un job-shop 3×3, puis le résout par OR-Tools | Après 03 ; goût pour les contraintes | 08 |
| 08 | [Planners-08-Temporal-Python](03-Advanced/Planners-08-Temporal-Python.ipynb) · [C#](03-Advanced/Planners-08-Temporal-Csharp.ipynb) | PDDL 2.1 : actions duratives, parallélisme, contraintes temporelles simples et denses, ordonnancement. Le jumeau C# construit l'algèbre d'Allen, un réseau temporel simple et un RCPSP allégé, puis résout le RCPSP par CP-SAT | Après 07, ou 06 avec PDDL | 09 |
| 09 | [Planners-09-HTN-Python](03-Advanced/Planners-09-HTN-Python.ipynb) · [C#](03-Advanced/Planners-09-HTN-Csharp.ipynb) | Planification hiérarchique : tâches primitives et abstraites, méthodes de décomposition, HDDL, solveur inspiré de SHOP2. Le jumeau C# réécrit SHOP2, puis attaque le même problème par `unified-planning` et `aries` par pont .NET vers CPython | Après 06 ; récursivité | [Partie 4](04-NeuroSymbolic/README.md) |
| 10 | [Planners-10-LLM-Planning](04-NeuroSymbolic/Planners-10-LLM-Planning-Python.ipynb) | Le LLM comme planificateur direct : état, actions et prompt ; chaîne de raisonnement ; arbre de pensée, qui retient un plan sur les branches explorées ; traduction du langage naturel vers PDDL et validation du domaine généré ; réparation de plan ; le LLM employé comme heuristique plutôt que comme solveur | Une clé d'API de modèle de langage | [Palier 10b](#autour-de-10--le-llm-réducteur-despace) |
| 11 | [Planners-11-Unified-Planning](04-NeuroSymbolic/Planners-11-Unified-Planning-Python.ipynb) | Un problème décrit une fois, résolu par plusieurs moteurs : sur le même modèle, `pyperplan` et `fast-downward` rendent le même plan à des vitesses différentes. Actions duratives, fluents numériques et coûts — version optimisante contre version satisfaisante —, export et import PDDL | Après 04 ; `unified-planning` avec au moins deux moteurs | [Partie 3](03-Advanced/README.md) : les paradigmes que ces moteurs implémentent |
| 12 | [Planners-12-LOOP](04-NeuroSymbolic/Planners-12-LOOP-Python.ipynb) | *Learning to Plan* : encoder un état PDDL, réseaux de politique et de valeur, boucle d'entraînement, puis un banc jouet mesuré à l'exécution — l'imitation apprise couvre 60,0 % de 15 instances inédites, contre 33,3 % pour une politique aléatoire et 100 % pour le BFS exact. Encodage par graphe (GNN) et fonctions de noyau (KRCL) en complément | Après 05 ; PyTorch et notions de réseau de neurones | [Partie 2](02-Classical/README.md) : les heuristiques que l'on cherche ici à apprendre |
| 13 | [Planners-13-Mesure-Qualite-Plans](03-Advanced/Planners-13-Mesure-Qualite-Plans-Python.ipynb) | Mesurer ce que la qualité d'un plan doit à son heuristique : sur une tour de quatre blocs, cinq configurations de Fast Downward trouvent le plan optimal de six actions en évaluant de 22 à 121 états selon l'heuristique, une recherche gloutonne s'en écarte, et un BFS naïf en Python sert de contrepoint | Après 04 et 05 | [Partie 2](02-Classical/README.md) : la théorie des heuristiques |

## Approfondissements — Recherche

Chaque palier lettré ajoute une dimension à son numéro porteur et suppose un prérequis de plus que le parcours principal. Les jumeaux C# ne sont pas des approfondissements : ce sont les mêmes numéros dans un autre langage, et ils figurent sur la ligne de leur numéro.

### Autour de 05 — prouver l'admissibilité, mesurer une primitive

| Lettre | Notebook | Ce qu'elle ajoute | Prérequis en plus |
|---|---|---|---|
| 5b | [Planners-05b-Lean-Relaxation-Lean](02-Classical/Planners-05b-Lean-Relaxation-Lean.ipynb) | Companion natif à noyau Lean 4 : la preuve sans `sorry` de $h^{+} \leq h^{*}$ dans le lake `planning_lean`, vérifiée par `#check` et `#print axioms` dans le noyau, avec les lemmes de monotonie sur un domaine jouet exécutable | Noyau Lean 4 sous WSL, et le lake construit |
| 5c | [Planners-05c-Differentiel-Atteignabilite-Python](02-Classical/Planners-05c-Differentiel-Atteignabilite-Python.ipynb) | Différentiel d'atteignabilité : un protocole en quatre pas — inatteignabilité prouvée par énumération exhaustive, contrôle d'effort, primitive nommée et payante, delta mesuré — qui consomme les théorèmes du lake, dont la chaîne $h_{max} \leq h^{+} \leq h^{*}$ | Python standard, sans Docker |

### Autour de 10 — le LLM réducteur d'espace

[Planners-10b-LLM-Space-Reducer](04-NeuroSymbolic/Planners-10b-LLM-Space-Reducer-Python.ipynb) prend le contrepied du numéro 10 : le modèle de langage n'y résout rien, il **réduit** l'espace que le solveur déterministe explorera. Sur un mini-langage de huit primitives typées agissant sur des grilles, l'espace des programmes de profondeur au plus quatre se compte en centaines de millions ; trois bras sont mesurés sur les mêmes tâches — recherche exhaustive bornée, LLM direct, LLM réducteur. Le réducteur désigne les primitives à essayer et ramène l'espace de plusieurs ordres de grandeur, avant que le même moteur déterministe n'y trouve les solutions. La correction reste au solveur : c'est la division du travail que la mesure rend visible.

## Sous-séries — découverte

La série est découpée en quatre parties, chacune dans son dossier et chacune avec son propre README au même format que celui-ci. Le parcours principal ci-dessus les traverse dans l'ordre : 03 ouvre la partie 1, 06 la partie 2, 09 la partie 3, 12 la partie 4.

| Dossier | Ce qu'on y apprend | Entrée | README |
|---|---|---|---|
| [00-Environment](00-Environment/) | L'installation et la vérification de l'environnement | [Planners-00-Setup](00-Environment/Planners-00-Setup-Python.ipynb) | — (un seul carnet) |
| [01-Foundation](01-Foundation/) | Le vocabulaire formel : État-Action-But, STRIPS, PDDL, espace d'états | [Planners-01-Introduction](01-Foundation/Planners-01-Introduction-Python.ipynb) | [README](01-Foundation/README.md) |
| [02-Classical](02-Classical/) | Résoudre : Fast Downward et la théorie des heuristiques | [Planners-04-Fast-Downward](02-Classical/Planners-04-Fast-Downward-Python.ipynb) | [README](02-Classical/README.md) |
| [03-Advanced](03-Advanced/) | Contourner l'explosion : contraintes, temps, hiérarchie | [Planners-07-OR-Tools](03-Advanced/Planners-07-OR-Tools-Python.ipynb) | [README](03-Advanced/README.md) |
| [04-NeuroSymbolic](04-NeuroSymbolic/) | Apprendre à chercher : modèle de langage, interface unifiée, *Learning to Plan* | [Planners-10-LLM-Planning](04-NeuroSymbolic/Planners-10-LLM-Planning-Python.ipynb) | [README](04-NeuroSymbolic/README.md) |

## Installation — pratique, tous niveaux

Ouvrir les carnets depuis un clone du dépôt : ils lisent `fast_downward_backend.py` et `requirements.txt` du dossier de la série.

- **Python 3.9+** : `pip install -r requirements.txt` installe `unified-planning`, `up-fast-downward`, `up-pyperplan`, `up-aries`, OR-Tools, NetworkX, Matplotlib, NumPy et PyTorch.
- **Fast Downward** : le paquet `up-fast-downward` embarque un moteur compilé, sans Docker. Le conteneur `jsboige/coursia-fast-downward` sur le port 8200 reste une option, et les carnets le préfèrent quand il répond. Le module `fast_downward_backend.py` choisit entre service et plugin, et sa première ligne de sortie nomme le moteur retenu.
- **Vérification** : `python -c "import unified_planning, up_fast_downward; from ortools.sat.python import cp_model; print('OK')"`.
- **Modèle de langage** : les carnets 10 et 10b interrogent un service externe et demandent une clé d'API dans l'environnement. Sans clé, les cellules d'appel échouent proprement : la lecture du raisonnement reste possible, l'exécution des appels non.
- **Lean** : le palier 5b demande un noyau Lean 4 sous WSL et le lake [`planning_lean`](planning_lean/README.md) construit avec sa toolchain.
- **.NET 9 Interactive** (jumeaux C#) : les tranches from-scratch s'exécutent seules ; les tranches moteur tirent des paquets NuGet — `QuikGraph` pour le jumeau 3, `Google.OrTools` pour 7 et 8, `pythonnet` pour 9, qui demande en plus un Python avec `unified-planning` et `up-aries`.

## Pour aller plus loin — recherche

### Formalisations Lean

Le lake [`planning_lean`](planning_lean/README.md) formalise l'admissibilité de la relaxation sans-delete : le coût du plan relaxé optimal ne dépasse jamais celui du plan réel optimal (`relaxed_plan_admissible`), avec un témoin associé (`relaxed_plan_witness`). Les paliers 5b et 5c le consomment en partie 2. Modules, pins et mesure des `sorry` vivent dans [`LEAN_INVENTORY.md`](LEAN_INVENTORY.md), qui n'est pas recopié ici.

### Ce que la mesure déplace

Le carnet 13 mesure ce qu'une heuristique achète à plan égal ; le palier 10b mesure ce qu'une réduction apprise apporte à un moteur déterministe, et à quel prix d'espace ; le carnet 12 mesure une couverture apprise contre un BFS exact sur des instances inédites. Ces trois-là laissent ouvertes les questions que la série rend manipulables : à quelle condition un modèle de langage est-il un planificateur plutôt qu'un générateur de texte plausible, que mesure exactement une couverture apprise face à un solveur complet, et où placer la frontière entre ce que l'on apprend et ce que l'on vérifie.

Une version antérieure du carnet 4 est conservée dans [`_archive/`](_archive/Fast-Downward-Legacy.ipynb), hors parcours.

### Ponts avec les autres séries

| Série | Ce que le pont apporte |
|---|---|
| [Search](../../Search/README.md) | BFS, DFS et A* de Search sont les briques des planificateurs classiques ; le CSP de Search est le même moteur que le CP-SAT du carnet 7 |
| [Lean](../Lean/README.md) | La vérification formelle certifie ce que la planification calcule ; le lake `planning_lean` en est l'application intra-série |
| [SmartContracts](../SmartContracts/README.md) | Les liquidations et l'arbitrage sont des problèmes de planification sous contraintes temporelles et de coût |
| [GameTheory](../../GameTheory/README.md) | A* en planification et minimax en jeux partagent la même structure de graphe d'états ; la recherche adverse s'ajoute à la recherche mono-agent |
| [Tweety](../Tweety/README.md) | Les solveurs SAT et CSP de Tweety résolvent des sous-problèmes que la planification pose |

## Ressources — tous niveaux

### Documentation

- [unified-planning](https://github.com/aiplan4eu/unified-planning) — bibliothèque Python multi-moteurs
- [Fast Downward](https://www.fast-downward.org/) — planificateur de référence
- [PDDL Reference](https://planning.wiki/) — documentation du langage
- [OR-Tools CP-SAT](https://developers.google.com/optimization/cp/cp_sat) — solveur de contraintes
- [IPC Benchmarks](https://github.com/aibasel/downward-benchmarks) — problèmes standards

### Cours et tutoriels

- [AI Planning — University of Edinburgh](https://www.coursera.org/learn/ai-planning)
- [Classical Planning — Stanford](https://www.youtube.com/watch?v=WEDagb6TsK8)

### Publications

| Référence | Couverture |
|---|---|
| Ghallab, Nau et Traverso, *Automated Planning: Theory and Practice* (2004) | Ouvrage de référence de la série |
| Russell et Norvig, *AIMA*, 4e édition, chapitres 10 et 11 | Cadre général de la planification |
| Helmert, « The Fast Downward Planning System » (2006) | Carnets 4 à 6 |
| Hoffmann et Nebel, « The FF Planning System » (2001) | Heuristique h-FF, carnet 5 |
| Richter et Westphal, « LAMA: Planner » (2010) | Landmarks, carnet 5 |
| Fox et Long, « PDDL2.1 » (2003) | Carnet 8 |
| Erol, Hendler et Nau, « HTN Planning: Complexity and Expressivity » (1994) | Carnet 9 |
| Valmeekam et al., « On the Planning Abilities of Large Language Models » (2024) | Carnet 10 |

### Dans le dépôt

- [README de la série](../README.md) — l'arc au-dessus de Planners
- [Inventaire Lean de la série](LEAN_INVENTORY.md) — modules, pins et mesure des `sorry`
- [Principe des vitesses de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) — à la racine du dépôt

---

Voir la licence du dépôt principal. [↑ SymbolicAI](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
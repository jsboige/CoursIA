# Coalitions — pouvoir, assistance et affectation

[↑ GameTheory](../README.md) · [Entrée : jeux coopératifs](../GameTheory-15-CooperativeGames-Python.ipynb)

Que vaut un groupe de joueurs, et comment partager sa valeur ou organiser leur coopération ? Cette sous-série de [GameTheory](../README.md) explore le pouvoir dans les votes pondérés, l'assistance entre un humain et un agent, puis l'appariement et l'affectation de ressources. Elle relie des expériences Python à des certificats d'optimalité et à leur formulation en Lean.

Elle s'adresse aux étudiants en informatique, économie et mathématiques appliquées. [GameTheory-15 — Jeux coopératifs](../GameTheory-15-CooperativeGames-Python.ipynb) apporte les fonctions caractéristiques, la valeur de Shapley et le cœur d'un jeu. [GameTheory-16 — Conception de mécanismes](../GameTheory-16-MechanismDesign-Python.ipynb) introduit le vocabulaire des mécanismes utilisé pour l'appariement. Python suffit comme langage d'entrée ; la dernière étape demande aussi Lean et la lecture d'inégalités de dualité.

## Comment lire ce README — découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue parcours principal, approfondissements et prolongements de recherche.

- **Vous découvrez** : partez du parcours principal. Pouvoir et assistance se lisent après GameTheory-15 ; échange de reins, affectation et certificat Lean forment un second cheminement après GameTheory-16.
- **Vous approfondissez** : utilisez les exercices et les liens associés à chaque palier. Ce dossier ne comporte pas de carnet à numéro lettré.
- **Vous cherchez des prolongements** : consultez « Pour aller plus loin » pour les relations avec le choix social, les formalisations et les limites des bancs.

## Parcours principal — lecture guidée et prérequis

Le fil commun consiste à choisir **ce que l'on évalue**. Dans un vote, le poids nominal peut différer du pouvoir de faire basculer la décision. Dans un jeu d'assistance, la réussite dépend de ce que l'assistant apprend de l'objectif humain. Dans un appariement, maximiser le nombre de bénéficiaires, respecter une équité et empêcher des défections sont des objectifs distincts. Le certificat primal-dual de 04–05 permet enfin de justifier un optimum pour un problème d'affectation donné.

La colonne des prérequis rend explicites ces changements de profondeur. Les expériences de vote et d'appariement donnent une entrée concrète ; l'analyse du regret, les garanties SMT et la preuve Lean demandent une lecture avancée.

| # | Notebook | Ce qu'on y apprend | Public et prérequis | Pour approfondir |
|---|---|---|---|---|
| 01 | [Pouvoir coalitionnel et SMT](Coalitions-01-Pouvoir-Coalitionnel-SMT-Python.ipynb) | Distinguer poids d'un votant et pouvoir de faire basculer une décision ; comparer les indices de Shapley–Shubik, Banzhaf et Deegan–Packel par énumération et encodage SMT. | Jeux coopératifs, Python ; initiation à Z3 dans le carnet. | Joueurs nuls, symétrie et portée des résultats SAT/UNSAT. |
| 02 | [Jeux d'assistance](Coalitions-02-Assistance-Games-Python.ipynb) | Formaliser un objectif imparfaitement connu de l'assistant ; comparer un apprenant EXP3 à un oracle de politique jointe calculé a posteriori. | Jeux coopératifs ; probabilités et notion de regret. | Qualité du signal humain et évolution du regret avec l'horizon. |
| 03 | [Échange de reins](Coalitions-03-Echange-de-Reins-Lean-Python.ipynb) | Construire un graphe de compatibilité, examiner cycles et chaînes de dons, puis discuter cardinalité, équité et évolution d'une institution. | Mécanismes, graphes et Python. Le noyau est Python malgré le pont Lean annoncé par le nom. | Fiabilité des chaînes, frontière de Pareto et effets du mécanisme sur les interactions suivantes. |
| 04 | [Affectation de Kuhn–Munkres](Coalitions-04-Munkres-Affectation-Python.ipynb) | Comprendre la méthode hongroise, construire un certificat primal-dual à gap nul et relier l'affectation au jeu coopératif de Shapley–Shubik. | Matrices de coûts, Python ; introduction à la dualité linéaire dans le carnet. | Comparer stabilité de Gale–Shapley et coût optimal ; poursuivre en 05. |
| 05 | [Affectation en Lean](Coalitions-05-Lean-Affectation-Lean.ipynb) | Lire et utiliser les énoncés de dualité faible, d'optimalité à gap nul et de maintien de la faisabilité duale. | Après 04 ; Lean et compréhension du certificat primal-dual. | [Formalisations Lean](#formalisations-lean) et exercices sur les certificats. |

## Approfondissements — Licence et lectures avancées

Les approfondissements se trouvent ici dans les carnets eux-mêmes. Le palier 01 permet de construire des jeux où poids et pouvoir divergent. Le palier 02 interroge ce qu'un assistant peut apprendre d'un signal humain peu informatif. Autour de 03, les exercices font varier les contraintes du mécanisme ; autour de 04–05, ils portent sur le certificat qui justifie l'affectation.

Le passage de 04 à 05 est une progression explicite : le carnet Python calcule et vérifie des instances, puis le carnet Lean expose les hypothèses et les énoncés formels. Ils conservent leurs numéros distincts et se lisent dans cet ordre.

## Installation — pratique, tous niveaux

Travailler dans un clone du dépôt pour rendre accessibles les modules locaux [cooperative_games](../cooperative_games/). Depuis le dossier GameTheory, installer les dépendances Python déclarées dans [requirements.txt](../requirements.txt), puis ouvrir les carnets avec un noyau Python compatible : le fichier complet demande Python 3.11 ou ultérieur, notamment pour PyArrow. Les usages comprennent notamment NumPy, SciPy, Pandas et Z3 ; suivre les cellules de préparation et les [instructions de la famille](../README.md).

Le carnet 02 construit son chemin d’import local depuis le répertoire de travail : lancer Jupyter depuis la racine du dépôt ou rendre `MyIA.AI.Notebooks/GameTheory` accessible dans `PYTHONPATH`.

L’expérience d’optimisation du carnet 03 utilise aussi PuLP et son solveur CBC, absents du fichier de dépendances commun ; sans eux, la cellule saute cette expérience. Le carnet 03 lit également des sources formelles : leur lecture ne constitue pas une construction du projet Lean. Le carnet 05 utilise, lui, un noyau Lean natif et exige la préparation du projet [assignment_lean](../assignment_lean/README.md) avec sa toolchain.

## Pour aller plus loin — recherche

### Interpréter les expériences

- **Pouvoir de vote** : les vérifications SMT concernent les tailles et encodages annoncés. Une photographie de poids parlementaires ne mesure pas la discipline de vote ni la fréquence effective des coalitions.
- **Assistance** : EXP3 est évalué sur une instance synthétique face à un oracle a posteriori. La comparaison empirique des courbes de regret ne constitue pas une borne générale démontrée pour cette implémentation.
- **Appariement** : une contrainte d'équité peut préserver la cardinalité sur l'exemple affiché ; ce résultat dépend de l'instance. Les exercices non complétés restent des activités proposées au lecteur.
- **Affectation** : les contrôles numériques croisent plusieurs méthodes sur les matrices du banc. Gale–Shapley cherche la stabilité et Kuhn–Munkres minimise un coût ; une coïncidence de résultats ne rend pas leurs objectifs équivalents.

### Formalisations Lean

Le projet [assignment_lean](../assignment_lean/README.md) fournit les définitions et certificats consommés en 05 : `Assignment.value`, `DualFeasible`, `weak_duality`, `optimality_of_zero_gap`, `kuhn_munkres_correct` et `dualFeasible_tighten`. Le carnet présente leurs énoncés et leurs dépendances axiomatiques, puis les applique à des exemples. Les toolchains et l'inventaire des projets sont centralisés dans [LEAN_INVENTORY.md](../LEAN_INVENTORY.md).

### Liens avec les autres parcours

La décomposition de Möbius et les dividendes de Harsanyi prolongent l'étude des coalitions dans [SocialChoice](../SocialChoice/README.md). La valeur de Shapley, le cœur et la condition de Bondareva–Shapley se lisent dans [GameTheory-15](../GameTheory-15-CooperativeGames-Python.ipynb) et son [approfondissement Lean](../GameTheory-15b-Lean-CooperativeGames-Lean.ipynb). Pour les mécanismes d'Othman–Sandholm et les populations d'agents de langage, repartir de [GameTheory-16](../GameTheory-16-MechanismDesign-Python.ipynb) et des approfondissements présentés dans la [série mère](../README.md).

## Ressources — tous niveaux

Les sources sont présentées auprès des expériences : indices de pouvoir et garanties SMT dans [01](Coalitions-01-Pouvoir-Coalitionnel-SMT-Python.ipynb), jeux d'assistance étudiés par Ananthakrishnan et ses coauteurs dans [02](Coalitions-02-Assistance-Games-Python.ipynb), mécanismes d'échange dans [03](Coalitions-03-Echange-de-Reins-Lean-Python.ipynb), méthode hongroise et jeu d'affectation de Shapley–Shubik dans [04](Coalitions-04-Munkres-Affectation-Python.ipynb).

[Retour à GameTheory](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)

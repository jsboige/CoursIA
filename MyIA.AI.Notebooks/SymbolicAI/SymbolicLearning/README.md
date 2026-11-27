# SymbolicLearning - Apprentissage Symbolique

[← ArgumentAnalysis](../ArgumentAnalysis/README.md) | [↑ SymbolicAI](../README.md) | [SMT →](../SMT/README.md)

<!-- CATALOG-STATUS
series: SymbolicAI-SymbolicLearning
pedagogical_count: 28
breakdown: SymbolicLearning=28
maturity: BETA=26, ALPHA=2
-->

## Découverte — apprendre à partir de connaissances, pas seulement de données

Comment un agent peut-il apprendre à partir de connaissances existantes plutôt que de données brutes ? C'est la question du chapitre 19 d'AIMA (Russell et Norvig), *Knowledge in Learning*. La série la déroule jusqu'aux travaux de recherche : apprendre un concept dans un espace d'hypothèses, guider l'apprentissage par une théorie du domaine (EBL, RBL), induire des programmes logiques et faire tourner les moteurs réels, rendre la logique différentiable, miner des règles sur un graphe de connaissances, faire proposer des règles par un LLM puis les vérifier, apprendre un automate par requêtes, assembler ces briques dans un capstone, puis des carnets de recherche.

### À qui cette série s'adresse

Étudiants en IA, informaticiens intéressés par le raisonnement symbolique, et chercheurs en apprentissage automatique souhaitant comprendre les approches non-statistiques.

Trois connaissances suffisent pour entrer : Python de base (fonctions, classes, tuples, dictionnaires) ; logique propositionnelle (conjonctions, prédicats) ; notions d'apprentissage supervisé (classification binaire). Une familiarité avec la logique propositionnelle suffit pour les carnets 01 à 06 et 10 ; les carnets 07, 09 et 11 supposent une intuition des réseaux de neurones et des LLM.

Plusieurs carnets ont un jumeau C# (.NET Interactive) : mêmes algorithmes, plus un pont vers un moteur de production ou un solveur de référence. Les jumeaux figurent sur la ligne de leur carnet dans le parcours ; ce qu'ils ajoutent est détaillé en [Jumeaux C#](#jumeaux-c).

### Pourquoi une série sur l'apprentissage symbolique

Trois situations où les données seules ne suffisent pas :

- **Peu de données disponibles** : les méthodes symboliques comme Candidate Elimination ou FOIL apprennent à partir de quelques exemples, voire d'un seul (EBL). Quand la collecte de données est coûteuse ou impossible (diagnostic médical rare, validation formelle), l'induction pure ne fonctionne pas.
- **Interprétabilité requise** : une règle logique `IF temperature > 38 AND toux THEN infection` est compréhensible par un humain. Un réseau de neurones de cent millions de paramètres ne l'est pas. Pour les applications critiques ou réglementées (médecine, finance, justice), l'interprétabilité n'est pas un luxe, c'est une exigence.
- **Intégration avec la connaissance existante** : les méthodes symboliques combinent exemples ET théorie du domaine. EBL compile un exemple prouvé en une règle opérationnelle générale ; RBL identifie les attributs déterminants par des contraintes formelles. Aucune méthode statistique n'exploite cette connaissance a priori de la même façon.

Le fil rouge de la série : l'apprentissage symbolique réussit là où les données seules échouent, non pas en ignorant la connaissance, mais en l'écrivant explicitement, en l'induisant des exemples, puis en la réconciliant avec le connexionnisme. Le geste profond : transformer une théorie du domaine (une détermination, une preuve, une ontologie) en un programme qui apprend, et montrer au capstone que l'on peut tenir les deux bouts, LLM et logique, dans une même boucle où chacun corrige l'autre.

## Comment lire ce README

Un README de série se lit à plusieurs vitesses : le parcours par les numéros nus, l'approfondissement par les lettres, puis les carnets de recherche et les ressources. Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous découvrez** : suivez le [parcours principal](#parcours-principal), du carnet 01 au carnet 11 ; les carnets 12 à 15 sont des carnets de recherche, à lire après.
- **Vous creusez un palier** : les extensions lettrées vivent en [Approfondissements](#approfondissements), sous le numéro qu'elles prolongent ; elles ne sont pas une autre version du carnet principal.
- **Vous cherchez la recherche en cours** : [Questions de recherche ouvertes](#questions-de-recherche-ouvertes), [Ce que les carnets mesurent](#ce-que-les-carnets-mesurent), puis [Ressources](#ressources).

## Parcours principal

| # | Notebook | Ce qu'on y apprend | Public et prérequis | Pour approfondir |
|---|----------|--------------------|----------------------|------------------|
| 01 | [Apprentissage logique : CBH Search et Version Space](SL-01-LogicalLearning-Python.ipynb) · [jumeau C#](SL-01-LogicalLearning-CSharp.ipynb) | Sur le problème du restaurant d'AIMA, représenter une hypothèse comme une conjonction de contraintes sur les attributs, l'apprendre par Current-Best-Hypothesis puis par Candidate Elimination et son espace de versions (bornes G et S), lire les limites de ce cadre face au bruit et aux disjonctions, et confronter l'implémentation à la référence aima-python. | Découverte · logique propositionnelle | [Compagnon Lean](#autour-de-01--compagnon-lean-et-note-de-lecture) |
| 02 | [Apprentissage et connaissance (EBL & RBL)](SL-02-KnowledgeBasedLearning-Python.ipynb) · [jumeau C#](SL-02-KnowledgeBasedLearning-CSharp.ipynb) | Compiler un exemple résolu en règle réutilisable par Explanation-Based Learning et ses quatre étapes (expliquer, variabiliser, extraire, simplifier), sur l'exemple de Zog et sur l'arithmétique ; mesurer ce que les règles économisent en étapes et ce qu'elles coûtent en temps ; introduire Relevance-Based Learning et les déterminations, approfondies au carnet 03. | Découverte · carnet 01, logique du premier ordre | — |
| 03 | [Apprentissage basé sur la pertinence](SL-03-RelevanceLearning-Python.ipynb) · [jumeau C#](SL-03-RelevanceLearning-CSharp.ipynb) | Chercher les attributs pertinents par la logique plutôt que par les statistiques : déterminations et treillis des déterminations, algorithme MINIMAL-CONSISTENT-DET, et comparaison avec une sélection par information mutuelle (scikit-learn). | Licence · carnets 01 et 02 | — |
| 04 | [Programmation logique inductive (ILP)](SL-04-InductiveLogicProgramming-Python.ipynb) · [jumeau C#](SL-04-InductiveLogicProgramming-CSharp.ipynb) | Apprendre des clauses de Horn récursives : clauses et unification, FOIL et son gain, résolution inverse (bottom-up) et ses opérateurs V et W ; confronter FOIL au moteur Popper (Learning From Failures) et faire le pont vers les règles AMIE sur les graphes de connaissances (règle de Horn et `CONSTRUCT` SPARQL). | Licence · carnets 01 à 03 | — |
| 05 | [Résolution inverse et Progol (ILP bottom-up)](SL-05-InverseResolution-Python.ipynb) · [jumeau C#](SL-05-InverseResolution-CSharp.ipynb) | Pousser la voie bottom-up jusqu'à Progol : généralisation la moins générale (LGG) de Plotkin et son inflation, θ-subsomption, clause bottom par entailment inverse, recherche de la meilleure clause consistante ; la mise en œuvre de référence, Aleph, tourne sous SWI-Prolog. | Licence · carnet 04 | — |
| 06 | [Moteurs ILP modernes : Aleph, Metagol, Popper et dILP](SL-06-ModernILP-Python.ipynb) · [jumeau C#](SL-06-ModernILP-CSharp.ipynb) | Faire tourner les moteurs réels sur une même tâche récursive, distinguer leurs paradigmes (entailment inverse, méta-interprétation, contraintes, descente de gradient), lire l'invention de prédicats auxiliaires, et choisir un moteur selon la tâche (exactitude symbolique ou robustesse au bruit). | Licence · carnet 04 | — |
| 07 | [Intégration neuro-symbolique](SL-07-NeuroSymbolic-Python.ipynb) | Rendre la logique différentiable : t-normes et t-conormes, prédicats neuronaux, un mini DeepProbLog, puis la vraie bibliothèque LTNtorch ; les règles guident l'entraînement et la satisfaction des formules se lit dans la perte. | Licence · carnets 01 à 05, intuition des réseaux de neurones | — |
| 08 | [ILP moderne et knowledge graphs](SL-08-KnowledgeGraphs-ILP-Python.ipynb) · [jumeau C#](SL-08-KnowledgeGraphs-ILP-CSharp.ipynb) | Extraire des règles d'un graphe de connaissances RDF (rdflib) à la manière d'AMIE (support, confiance, confiance PCA), les valider, les appliquer pour compléter le graphe, et recouper le résultat par un chaînage avant Datalog sous clingo. | Licence · carnet 04, rudiments de RDF | — |
| 09 | [LLMs et apprentissage symbolique : génération et vérification d'hypothèses](SL-09-LLM-SymbolicLearning-Python.ipynb) | Utiliser un LLM comme proposeur d'hypothèses : vérification formelle des règles proposées, retour des erreurs pour une nouvelle génération, pipeline complet des exemples aux règles validées ; comparer le prompt direct au raisonnement pas à pas et mesurer la stabilité des règles d'une exécution à l'autre. | Licence · carnets 01 à 04, notions de LLM | — |
| 10 | [Apprentissage actif d'automates (L* d'Angluin)](SL-10-ActiveAutomataLearning-Python.ipynb) · [jumeau C#](SL-10-ActiveAutomataLearning-CSharp.ipynb) | Apprendre un automate sans voir sa table : L* pose des requêtes d'appartenance et d'équivalence à un oracle, tient une table d'observation fermée et consistante et converge vers l'automate minimal (Myhill-Nerode) ; variations Maler-Pnueli et Rivest-Schapire, puis oracle bruité, où l'agrégation de plusieurs observations récupère le langage. | Licence · carnets 01 et 03 | — |
| 11 | [Capstone : un pipeline neuro-symbolique de bout en bout](SL-11-Capstone-NeuroSymbolic-Python.ipynb) | Assembler la série en un pipeline : extraction de triplets par un LLM, oracle de validation symbolique, graphe de connaissances, mining de règles, chaînage avant avec provenance, confrontation du LLM seul au graphe raisonné. Un exercice rejoue le poison, un fait faux accepté par l'oracle, et le bloque par une contrainte de cardinalité. | Licence · carnets 01 à 10 | — |
| 12 | [Differentiable Logic Gate Networks](SL-12-DifferentiableLogicGateNetworks-Python.ipynb) | Remplacer les neurones par des portes logiques différentiables (bibliothèque difflogic), entraîner par descente de gradient, discrétiser en un circuit booléen pur et l'évaluer sur MNIST en 20 × 20 pixels. | Recherche · PyTorch | [Synthèse spectrale, reproduction](#autour-de-12--synthèse-spectrale-et-reproduction) |
| 13 | [DISCOVER léger : diagnostic de structure TPR émergente](SL-13-Discover-TPR-Python.ipynb) | Demander si un GRU à une couche, entraîné sur des tâches symboliques de séquence (copie, renversement, entrelacement), porte une structure de produit tensoriel (rôle × contenu) : remplacer l'état caché par son approximation et mesurer la perte, avec un contrôle contre des embeddings atomiques. Le périmètre est borné : une structure approximative, pas un produit tensoriel exact. | Recherche · PyTorch, CPU suffisant | [Dictionnaire creux, exécutions conservées](#autour-de-13--dictionnaire-creux-et-exécutions-conservées) |
| 14 | [AI Feynman : découvrir des équations](SL-14-AIFeynman-Discover-Equations-Python.ipynb) | Retrouver une équation à partir de données seules avec AI Feynman 2.0 : tests de séparabilité par les dérivées d'un réseau, longueur de description en bits, front de Pareto complexité-précision, sur l'énergie relativiste E(m, v). | Recherche · conteneur dédié (voir Installation) | — |
| 15 | [Conjectures apprises pour un vérificateur symbolique](SL-15-LearnedConjectures-Solver-Python.ipynb) | Transposer la boucle générateur/oracle du carnet 09 à un solveur CP-SAT : un modèle appris propose des fixations de variables (indications, ou hints) pour la coloration de graphe, le solveur les prend comme point de départ et signale leurs conflits, et la boucle apprend à les réparer ; une seconde famille (couverture d'ensemble) montre que le mécanisme se transporte, mais pas le geste de réparation. | Recherche · carnet 09 | — |

![Automate fini déterministe à 4 états (ee/oe/oo/eo) cible de l'algorithme L* d'Angluin : chaque état code une classe de parité (mod 2 × mod 2) sur la suite de symboles `a`/`b` lue](assets/readme/sl10-dfa-target.png)

*L'automate cible du carnet 10, que l'apprenant ne voit pas : quatre états, un seul acceptant (`ee`), un par classe de parité. Rendu du bloc `mermaid stateDiagram-v2` du carnet ; provenance et contenu de l'image documentés dans [MANIFEST.md](assets/readme/MANIFEST.md).*

### Parcours alternatifs

- **Parcours rapide** : carnets 01, 07, 09 et 11, pour voir le fil complet en quatre étapes.
- **ILP approfondi** : carnets 01 à 06.
- **Théorie des langages** : carnets 01 et 10, de l'espace d'hypothèses conjonctives à l'automate appris.
- **Graphes de connaissances** : carnets 02, 03, 04 et 08 (rdflib et AMIE ; une familiarité avec RDF et SPARQL aide).

### Séance de restitution

Modalité de la séance : chaque groupe choisit un exercice, le prépare et le présente. Résoudre l'exercice est le minimum attendu ; chaque exercice est assorti d'une question-twist (détaillée dans la section « Defi presentation » du carnet correspondant), qui fait partie intégrante de la présentation. Premier arrivé, premier servi : annoncez votre choix pour éviter les doublons. Dans le carnet 07, le premier exercice est un exemple guidé, solution démontrée ; piochez parmi les suivants.

## Approfondissements

Les extensions lettrées creusent un palier du parcours ; elles ne le font pas avancer.

### Autour de 01 — Compagnon Lean et note de lecture

Niveau Licence (compagnon du carnet 01).

- [01b — Apprentissage PAC formellement : le lake `learning_theory_lean` exécuté en noyau Lean](SL-01b-LogicalLearning-Lean.ipynb) : les mêmes notions passées en théorie formelle — vocabulaire PAC, échantillon i.i.d., borne de généralisation d'une classe finie, cadre agnostique, concentration de Markov à Hoeffding — puis le perceptron (convergence de Novikoff et serrage de la borne). Il s'exécute en noyau Lean sur le lake [`learning_theory_lean`](../../ML/learning_theory_lean/README.md) ; il ne fait pas partie du parcours exécutable en Python.
- [Note de lecture — AIMA, chapitre 19](reference/AIMA_Ch19_Knowledge_in_Learning.md) : la synthèse du chapitre *Knowledge in Learning* de Russell et Norvig.
- [`reference/aima_knowledge.py`](reference/aima_knowledge.py) : un sous-ensemble vendu de `knowledge.py` d'aima-python (licence MIT, copyright 2016 aima-python contributors), avec Current-Best-Hypothesis, Candidate Elimination et MINIMAL-CONSISTENT-DET ; il est testé par [`tests/test_aima_knowledge.py`](tests/test_aima_knowledge.py).

### Autour de 12 — Synthèse spectrale et reproduction

Niveau Recherche.

- [12b — Synthèse logique spectrale : Fourier booléen et poids ternaires](SL-12b-SpectralLogicSynthesis-Python.ipynb) · [jumeau C#](SL-12b-SpectralLogicSynthesis-CSharp.ipynb) : au lieu d'apprendre des portes, représenter une fonction booléenne par ses caractères de Walsh et en sélectionner les coefficients — poids ternaires, polynômes à seuil ternaire, routage par Sinkhorn, recherche discrète (balayage glouton, énumération exhaustive).
- [12c — Pavlov DLS : reproduction](SL-12c-PavlovDLS-Reproduction-Python.ipynb) : la reproduction du papier de Pavlov sur CPU, linéaire signé contre Sinkhorn contraint, qui ne confirme pas le gain mesuré pour Sinkhorn (voir [Questions de recherche ouvertes](#questions-de-recherche-ouvertes)) ; [exécution conservée](SL-12c-PavlovDLS-Reproduction-output-Python.ipynb) du même carnet, aux cellules identiques.

### Autour de 13 — Dictionnaire creux et exécutions conservées

Niveau Recherche.

- [13b — TPR x SAE : deux lectures des mêmes états cachés](SL-13b-TPR-SAE-Python.ipynb) : suite directe du carnet 13, qui relit les mêmes états cachés avec un auto-encodeur à dictionnaire creux et mesure l'effet causal des atomes dédiés.
- [Exécution conservée du carnet 13](SL-13-Discover-TPR-output-Python.ipynb) : une exécution antérieure du carnet, conservée avec ses sorties ; une partie de ses cellules a depuis changé, et le carnet principal est celui à lire.

## Jumeaux C#

Les jumeaux C# (.NET Interactive) reprennent les algorithmes de leur carnet Python et ajoutent chacun un pont vers un moteur de production ou un solveur de référence.

| Carnet | Jumeau | Ce qu'il ajoute |
|--------|--------|------------------|
| 01 | [SL-01 C#](SL-01-LogicalLearning-CSharp.ipynb) | CBH et Candidate Elimination écrits à la main en C# pur (système de types et `HashSet<>`, sans bibliothèque de ML). |
| 02 | [SL-02 C#](SL-02-KnowledgeBasedLearning-CSharp.ipynb) | EBL par chaînage avant avec unification (arbre de preuve, variabilisation) et RBL par vérification de détermination ; mesure du gain. |
| 03 | [SL-03 C#](SL-03-RelevanceLearning-CSharp.ipynb) | Déterminations, treillis, clé minimale, borne PAC et parallèle avec OWL écrits à la main, puis un moteur de production : l'importance des variables par permutation sous ML.NET confirme le classement. |
| 04 | [SL-04 C#](SL-04-InductiveLogicProgramming-CSharp.ipynb) | Clauses de Horn et unification, FOIL pas à pas, résolution inverse, ILP sur un mini graphe de connaissances ; parité vérifiée avec clingo sur `ancestor/2`. |
| 05 | [SL-05 C#](SL-05-InverseResolution-CSharp.ipynb) | LGG de Plotkin, θ-subsomption, clause bottom par saturation bornée, recherche Progol sur `grandmother/2` ; parité vérifiée avec SWI-Prolog. |
| 06 | [SL-06 C#](SL-06-ModernILP-CSharp.ipynb) | Le noyau algorithmique FOIL (gain de Quinlan, couverture extensionnelle, récursion), un benchmark sur un graphe `parent` croissant et un verdict de portabilité des quatre moteurs du carnet Python ; parité vérifiée avec clingo. |
| 08 | [SL-08 C#](SL-08-KnowledgeGraphs-ILP-CSharp.ipynb) | Le même graphe de connaissances familial avec dotNetRDF, le mining de règles à la main et la complétion ; la récursion et les contraintes d'intégrité sous clingo restent dans le carnet Python. |
| 10 | [SL-10 C#](SL-10-ActiveAutomataLearning-CSharp.ipynb) | L*, table d'observation et exécution complète sur le langage cible, avec les garanties de minimalité et de complexité ; écrit avec la seule bibliothèque standard de .NET. |
| 12b | [SL-12b C#](SL-12b-SpectralLogicSynthesis-CSharp.ipynb) | Walsh, coefficients exacts, poids ternaires, routage par Sinkhorn et recherche discrète (Metropolis, parallel tempering) aux mêmes budgets ; Math.NET fait les moindres carrés du port C#, les générateurs aléatoires diffèrent et les figures C# sont des SVG statiques. |

## Sous-séries

Cette série n'a pas de sous-série.

## Installation

### Environnement Python

Les dépendances sont listées dans [requirements.txt](requirements.txt) ; par carnet :

- carnets 01 et 02 : bibliothèque standard de Python uniquement ;
- carnet 03 : `numpy` et `scikit-learn` ;
- carnet 04 : `clingo`, `janus_swi` et Popper, sous un noyau Linux (voir plus bas) ;
- carnet 05 : `janus_swi`, pour la section Aleph (optionnelle) ;
- carnet 06 : `clingo`, `janus_swi`, Popper et `matplotlib`, sous un noyau Linux ; l'ILP différentiable tourne à part, dans l'environnement `lernd-dilp` (voir plus bas) ;
- carnet 07 : `numpy`, `torch` et LTNtorch (`pip install LTNtorch`, et non `pip install ltn`, qui est un homonyme fondé sur TensorFlow avec une autre API) ;
- carnet 08 : `rdflib` et `clingo` (module Python officiel Potassco, installé silencieusement par le carnet) ;
- carnets 09 et 11 : `openai` et `python-dotenv` ;
- carnet 10 : `matplotlib` ;
- carnets 12, 13 et 13b : `numpy`, `torch` et `matplotlib` ; le carnet 12 ajoute `difflogic` et `torchvision`, le carnet 13b le paquet `ict` ;
- carnets 12b et 12c : `numpy`, et `matplotlib` pour le 12b ;
- carnet 14 : le paquet `aifeynman` n'est plus installable tel quel sur l'interpréteur actuel de la flotte (son `setup.py` importe `numpy.distutils`) : le carnet s'exécute dans le conteneur construit par [`assets/Dockerfile.aifeynman-py313`](assets/Dockerfile.aifeynman-py313), qui rend l'environnement fidèle au paquet figé en 2021 ;
- carnet 15 : `numpy`, `ortools` et `scikit-learn`.

Aleph s'exécute via `janus_swi` sur SWI-Prolog ; Metagol est fourni dans [`vendor/metagol/`](vendor/metagol/), sous licence BSD-3 ; Popper tourne en sous-processus ; l'ILP différentiable (Lernd) tourne dans un environnement conda dédié, `lernd-dilp` (TensorFlow, licence GPL-3.0), importé et jamais vendu. Chaque moteur indisponible se signale proprement (drapeau `HAS_*`) sans interrompre le carnet. La section Aleph du carnet 05 ne tourne que sur un noyau Linux : son délai de garde repose sur `SIGALRM`.

Les carnets 09 et 11 lisent leur clé LLM dans un fichier `.env` construit depuis [`.env.example`](.env.example) ; sans clé, un générateur (carnet 09) ou un simulateur (carnet 11) déterministe prend le relais, et le carnet s'exécute intégralement.

### Noyaux Jupyter

- `python3` pour la majorité des carnets ;
- `python3-wsl` (Linux sous WSL) pour les carnets 04 et 06, qui appellent Popper ;
- `difflogic-sl12` pour le carnet 12 ;
- `lean4-wsl` pour le carnet 01b ;
- `.net-csharp` (.NET Interactive) pour les jumeaux C#.

### Dépannage

- **`rdflib` ne s'installe pas, ou plante sur les parsers RDF/XML** (carnet 08) : installez `lxml` comme repli (`pip install lxml`), ou passez par un environnement conda (`conda install -c conda-forge rdflib`).
- **`scikit-learn` manquant ou incompatible** (carnets 03 et 15) : `pip install -U scikit-learn numpy`.
- **`MemoryError` sur le treillis des déterminations** (carnet 03) : le treillis des déterminations croît exponentiellement avec le nombre d'attributs (l'exemple du carnet en a dix : `Sous-ensembles testes : 11 / 1023`) ; limitez l'analyse aux attributs les plus informatifs en premier.
- **Un carnet ne trouve pas son noyau** : `python -m ipykernel install --user --name python3 --display-name "Python 3"`, puis `pip install papermill`, et redémarrez le noyau avant une exécution complète.

## Organisation du dossier

Hormis les carnets, le dossier porte :

- [`assets/`](assets/) : la figure du parcours ([`readme/`](assets/readme/), avec le [`MANIFEST.md`](assets/readme/MANIFEST.md) qui documente sa provenance) et les Dockerfiles du carnet 14 ;
- [`reference/`](reference/) : la note de lecture du chapitre 19 d'AIMA et `aima_knowledge.py`, sous-ensemble vendu de `knowledge.py` d'aima-python ;
- [`tests/`](tests/) : les tests de ce fichier de référence ;
- [`vendor/`](vendor/) : Metagol pour le carnet 06 et difflogic pour le carnet 12 ;
- [`_archive/`](_archive/) : le registre de disposition et le lot daté du précurseur EML de SL-12, remplacé par le carnet 12 ;
- [`.env.example`](.env.example) : le modèle de configuration des carnets 09 et 11 ; [`requirements.txt`](requirements.txt) : les dépendances.

## Pour aller plus loin

### Questions de recherche ouvertes

- **Le gain de Sinkhorn ne se reproduit pas sur CPU** (carnet 12c) : la reproduction ne mesure aucun gain, sans pour autant invalider le papier — le gradient proxy peut être insuffisant, le gain peut n'apparaître qu'au-delà de deux variables ou avec une autre initialisation, ou le claim peut être partiellement surévalué. L'écart est rapporté, pas moyenné.
- **Structure TPR approximative, pas produit tensoriel exact** (carnets 13 et 13b) : la structure se lit dans les états cachés, mais rien ne montre qu'un GRU calcule un produit tensoriel, et le dépôt officiel de DISCOVER n'est pas exécuté ici. Le passage à des architectures de production (transformers profonds, grands vocabulaires, longues séquences) est hors de portée du dispositif.
- **Le mécanisme se transporte, le geste de réparation non** (carnet 15) : sur la couverture d'ensemble, retirer une contrainte fausse gagne et ajouter une nécessité oubliée coûte, là où la coloration de graphe réagit autrement — la boucle générateur/oracle n'est pas un remède universel.
- **La découverte d'équations reste bornée à son budget** (carnet 14) : la recherche est plafonnée, `tanh` n'est pas dans la base d'opérations, et les résultats valent pour les fonctions du jeu de test, pas pour l'ensemble du benchmark du papier.

### Ce que les carnets mesurent

Les valeurs ci-dessous sont des sorties committées des carnets, recopiées telles quelles ; l'accentuation et la casse y sont celles du code qui les imprime.

- **01** : `VS appris sur 4 exemples : |G|=3, |S|=1` et `Version Space complet : 7 hypotheses consistantes` ; le vote majoritaire des hypothèses restantes donne `5/8 corrects, 0 incertain`, et trois exécutions donnent `Hypotheses distinctes sur 3 seeds : 1/3`. Côté C#, `CBH accuracy : 5/8 = 62,5%` et `Version Space (vote) accuracy : 4/8 = 50,0%`.
- **02** : EBL ramène la recherche de `101 etapes` à `67 etapes` (`Reduction : 34 etapes (34%)`, `Speedup (ratio) : 1.51x`), alors qu'en temps mural la médiane sur vingt exécutions donne `Ratio (sans/avec) : 0.33x` : les règles coûtent plus qu'elles ne rapportent à cette échelle, cas d'école du problème d'utilité. Le jumeau C# mesure `Speedup = 42/8 = 5,25x`.
- **03** : MINIMAL-CONSISTENT-DET `TROUVE : {R1, R2} apres 11 tests`, soit `Sous-ensembles testes : 11 / 1023` et `Facteur de reduction : 256x` ; la sélection par déterminations atteint `accuracy = 0.969`, là où un tirage aléatoire moyen donne `0.142` (meilleur tirage : `0.969`). Côté C#, `I(logp ; activity) = 0,6100 bits`.
- **04** : FOIL retrouve `Regle : ancestor(x, y) :- parent(x, y).` puis la clause récursive ; le jumeau C# obtient `Gain FOIL : 5,390` et conclut `Verdict parite : FOIL from-scratch == clingo (SOTA) sur ancestor/2`.
- **05** : sur `grandfather/2`, la clause bottom a 9 littéraux et `56 candidats connectes`, et Progol retient `[Rule 1] [Pos cover = 4 Neg cover = 0]` ; le jumeau C# conclut `Verdict parite : theorie from-scratch == SWI-Prolog (SOTA) sur grandmother/2`.
- **06** : `Tous apprennent : ancestor(A,B):-parent(A,B). ancestor(A,B):-parent(A,C),ancestor(C,B).`, et `Seul Metagol introduit un predicat auxiliaire (ancestor_1 = grandparent).` Sur un jeu volontairement empoisonné, le jumeau C# rend `TP = 11 / 11   FN = 0   FP = 1`.
- **07** : la satisfaction globale des règles atteint `0.9242` à l'époque 400, et l'inférence sur un seul vrai grandparent rend `grandparent(Marie, Paul)   = 1.000`.
- **08** : le graphe de départ compte `Total triples : 47` ; la règle retenue a `Support=14, Confidence=1.00` et `Gain : +9 triples (de 5 a 14)`, que le chaînage avant rejoue (`Total triples : 56 (+9)`) — `apply_rules etait bien un chainage avant Datalog -- clingo le confirme.` La confiance PCA donne `5/8 = 0.62`.
- **09** : en prompt direct, `Regles validees   : 4` et `Regles rejetees   : 0`, avec `Couverture des positifs par les regles validees : 6/6` ; en raisonnement pas à pas, `Regles validees     : 6` mais `Regles rejetees     : 4` (`Taux d'acceptation : 6/10 (60%)`) ; la stabilité d'une exécution à l'autre vaut `Regles validees stables sur les 3 runs : 3/5 (stabilite 60%)`.
- **10** : L* rejette une conjecture sur contre-exemple (`Conjecture 1 : 2 etats -> contre-exemple 'ba'`) puis accepte la suivante (`Conjecture 2 : 4 etats -> ACCEPTEE`), et rend `DFA appris : DFA(4 etats, 1 acceptants)` avec `|S| = 13, |E| = 3, MQ posees = 55` ; la vérification exhaustive confirme `2047/2047 mots (longueur <= 10) identiques`. Avec un oracle bruité (`eps=.20`), l'agrégation de 25 observations remonte de `0.790` (une observation) à `0.998`.
- **11** : l'extraction rend `19 triplets`, avec `Rappel : 19/19 = 1.00` et `Precision : 19/19 = 1.00` ; un exercice rejoue le poison (un fait faux accepté par l'oracle) et le bloque par une contrainte de cardinalité sur le nombre de parents.
- **12** : le réseau discrétisé atteint `Accuracy test : 0.826 (8261/10000)` ; la compilation en circuit C échoue dans l'environnement du carnet (`CompiledLogicNet indisponible`, code de sortie 1), ce que le carnet documente au lieu de le masquer.
- **12b** : la recherche exhaustive `Exhaustive 3^11 = 177147 vecteurs en 0.13 s` trouve `92` optimums globaux à `E = 0`, tandis que le balayage glouton parti de `w_q` reste à `E final = 2/16` (minimum local) ; le jumeau C# compare les transformées de Walsh (`n=12 : naïf 0.155689s ; papillon 0.000249s ; ratio 625.3`).
- **12c** : sur 27 opérations de la phase 1, le linéaire signé passe et Sinkhorn régresse (`Linéaire suffit, Sinkhorn régresse : 27 opérations`, `Sinkhorn aide (Δsk-lin > 1pp) : 0 opérations`) ; l'exemple `AND` tombe de `acc ternaire = 100%` en linéaire à `25%` en Sinkhorn.
- **13** : remplacer l'état caché par son approximation TPR ne coûte rien (`Δacc (TPR) = 0.000`), là où la même substitution par un contrôle atomique coûte `Δacc (atomic) = 0.695`.
- **13b** : sur la tâche copy, le GRU atteint `val_acc=0.817 (hasard = 0.091)` ; le dictionnaire creux se reconstruit avec `FVU SAE : train = 0.0747 | val = 0.1023` ; les huit atomes dédiés ont tous un effet causal positif (`atomes dedies avec effet > 0 : 8/8`) contre `128/160` pour le contrôle apparié, et leur sélectivité corrèle avec cet effet (`rho = +0.551`).
- **14** : le front de Pareto tient `36 candidates, 0.0 a 163.5 bits` ; la séparabilité multiplicative de E(m, v) = g(m)·h(v) est détectée (`S[log|E|] = 0.0051`, seuil 0.1) et la séparabilité additive rejetée (`S[E] = 0.8857`) ; MEDL retrouve mieux les exposants que MSE (`MEDL : a = 0.562, b = 1.204` contre `MSE  : a = 0.466, b = 0.787`, pour des vrais paramètres a = b = 1).
- **15** : les indications apprises réduisent les branches de `delta median = -18.4 %`, effacent les conflits (`med=42 -> apres : med=0`) et aident toutes les instances (`aidantes  (delta<0) :  300  (100.0 %)`) ; sur des graphes de test de `aretes min=165 | med=168.5 | max=174`, le hint brut fait mieux que le réparé (`-15.9 %` contre `-5.4 %`), et le réparé coûte `+12.5 %` de branches par rapport au brut.

### Séries voisines

| Série | Ce qui s'y prolonge |
|-------|----------------------|
| [Tweety](../Tweety/README.md) | Les logiques formelles (propositionnelle, premier ordre) sur lesquelles reposent les hypothèses symboliques. |
| [SemanticWeb](../SemanticWeb/README.md) | RDFS et OWL formalisent les déterminations et les hiérarchies de généralité ; SW-02 donne les bases RDF utiles au carnet 08. |
| [Planners](../Planners/README.md) | EBL compile une théorie en règles opérationnelles, comme les heuristiques de planification. |
| [Lean](../Lean/README.md) | L'arbre de preuve d'EBL est analogue aux arbres de preuve de Lean 4. |
| [Search](../../Search/README.md) | Le benchmark agrégé des conjectures apprises vit dans App-33 ; la série porte aussi solveurs et métaheuristiques. |
| [Probas](../../Probas/README.md) · [GameTheory](../../GameTheory/README.md) | Décider sous incertitude : le complément probabiliste du capstone. |
| Lecture transversale | [`La mer qui monte`](../../../docs/cadrage/grothendieckian-lens.md) : grille de lecture grothendieckienne du dépôt (changement de représentation, certification A/B/C). |

Quatre suites naturelles après le carnet 11 :

- **Approfondir les fondations formelles** : Tweety pour les logiques formelles et Lean pour les preuves ; les carnets 04 et 05 y trouvent leur ancrage rigoureux.
- **Passer à l'échelle sur le web de données** : SemanticWeb, naturellement après le carnet 08 (graphes de connaissances et AMIE).
- **Décider sous incertitude** : Probas (Infer.NET) et GameTheory, le complément probabiliste du capstone.
- **Du capstone à la production** : reprendre le pipeline du carnet 11 et remplacer l'oracle de validation par une vérification Lean ou une cohérence Tweety.

### Formalisations Lean

Le lake [`learning_theory_lean`](../../ML/learning_theory_lean/README.md), hébergé par la série [ML](../../ML/README.md), porte en théorèmes les notions du carnet 01b : cadre PAC de Valiant (borne d'échantillonnage d'une classe finie, cadre agnostique), convergence du perceptron (Novikoff, serrage de la borne), théorie effective, structures, générateurs et renommage. Le carnet 01b exécute ce lake en noyau Lean ; ces formalisations ne font pas partie du parcours.

## Concepts clés

| Concept | Explication | Notebook |
|---------|-------------|----------|
| **Hypothèse FOL** | Conjonction de contraintes sur les attributs | SL-01 |
| **Version Space** | Ensemble de toutes les hypothèses consistantes | SL-01 |
| **CBH** | Maintient une seule hypothèse ajustée incrémentalement | SL-01 |
| **Borne PAC** | Nombre d'exemples suffisant pour généraliser une classe finie d'hypothèses | SL-01b |
| **Perceptron (Novikoff)** | Convergence et serrage de la borne sur le nombre d'erreurs | SL-01b |
| **EBL** | Extrait une règle générale d'un seul exemple par déduction | SL-02 |
| **RBL** | Identifie les attributs pertinents via les déterminations | SL-02 |
| **Détermination** | Relation fonctionnelle entre attributs | SL-02, SL-03 |
| **KBIL** | Apprentissage inductif guidé par la connaissance | SL-02 |
| **Treillis des déterminations** | Ensemble partiellement ordonné des sous-ensembles d'attributs | SL-03 |
| **MINIMAL-CONSISTENT-DET** | Trouve la détermination minimale par taille croissante | SL-03 |
| **FOIL** | Apprentissage top-down de clauses Horn | SL-04 |
| **Résolution inverse** | Apprentissage bottom-up par opérateurs V et W | SL-04 |
| **Clause Horn** | Règle logique avec au plus un littéral positif | SL-04 |
| **Unification** | Trouve une substitution rendant deux termes égaux | SL-04 |
| **ILP** | Apprentissage de programmes logiques a partir d'exemples | SL-04 |
| **Learning From Failures (Popper)** | ILP moderne : recherche de programme optimal par contraintes (clingo + Prolog) | SL-04 |
| **LGG** | Généralisation la moins générale de deux clauses (Plotkin) | SL-05 |
| **Theta-subsomption** | Ordre de généralité décidable entre clauses (∃θ : Cθ ⊆ D) | SL-05 |
| **Clause bottom** | Clause la plus spécifique couvrant un exemple (entailment inverse) | SL-05 |
| **Progol** | Recherche de clause guidée par la clause bottom | SL-05 |
| **Aleph** | Entailment inverse, l'implémentation de référence de Progol (SWI-Prolog) | SL-05, SL-06 |
| **Metagol (MIL)** | Apprentissage meta-interpretatif : métarègles + invention de prédicats | SL-06 |
| **dILP** | ILP différentiable : règles pondérées apprises par descente de gradient | SL-06 |
| **T-norm** | Généralisation différentiable de AND | SL-07 |
| **DeepProbLog** | Programmation logique probabiliste + prédicats neuronaux | SL-07 |
| **Knowledge Graph** | Graphe orienté de triples (sujet, prédicat, objet) | SL-08 |
| **AMIE** | Rule mining sur knowledge graphs incomplets | SL-08 |
| **PCA confidence** | Confiance ajustée à l'incomplétude du graphe : dénominateur restreint aux sujets ayant au moins un prédicat de tête connu | SL-08 |
| **LLM-Symbolique** | Boucle de rétroaction LLM + vérification formelle | SL-09 |
| **Apprentissage actif** | L'apprenant choisit ses questions au lieu de subir un échantillon | SL-10 |
| **MAT** | Minimally Adequate Teacher : oracle d'appartenance + équivalence | SL-10 |
| **Table d'observation** | Structure (S, E, T) fermée et cohérente dont on lit un DFA | SL-10 |
| **Myhill-Nerode** | Classes d'équivalence de suffixes = états du DFA minimal | SL-10 |
| **Provenance** | Trace de dérivation attachée à chaque fait inféré | SL-11 |
| **Pipeline neuro-symbolique** | LLM aux extrémités, validation et inférence symboliques au centre | SL-11 |
| **Porte logique différentiable** | Neurone dont la fonction est une porte logique relaxée, discrétisée après entraînement | SL-12 |
| **Caractère de Walsh** | χ_S(x) = ∏_{k∈S} x_k — base orthonormée des fonctions {−1,+1}^n | SL-12b |
| **PTF ternaire** | sign(Σ w_S χ_S) avec w ∈ {−1,0,+1} — objet distinct des coefficients de Fourier exacts | SL-12b |
| **Routage Sinkhorn** | Projection itérative vers le polytope de Birkhoff ; dans l'exemple à blocs ex-aequo, la limite n'est pas une permutation | SL-12b |
| **TPR** | Représentation par produit tensoriel : somme de paires rôle × contenu | SL-13, SL-13b |
| **SAE (dictionnaire creux)** | Auto-encodeur à atomes épars, qui isole des directions interprétables | SL-13b |
| **MEDL** | Longueur de description moyenne de l'erreur : les valeurs aberrantes coûtent un logarithme, pas un carré | SL-14 |
| **CP-SAT** | Solveur de programmation par contraintes (OR-Tools) : statut et compteur de branches | SL-15 |
| **Hint** | Fixation partielle de variables proposée au solveur, qui reste libre de l'ignorer | SL-15 |

## Ressources

Références telles que les carnets les citent :

- Russell et Norvig, *Artificial Intelligence: A Modern Approach*, 3e et 4e éditions, chapitre 19 (*Knowledge in Learning*).
- Tom Mitchell, *Machine Learning*, chapitres 2 (Concept Learning) et 11 (Explanation-Based Learning).
- Minton (1990), sur le *utility problem* : des règles utiles peuvent coûter plus qu'elles ne rapportent (carnet 02).
- [AIMA Python Code](https://github.com/aimacode/aima-python), implémentations de référence.
- L. Valiant, *A Theory of the Learnable*, Communications of the ACM, 1984.
- S. Muggleton, *Inverse entailment and Progol*, New Generation Computing 13, 1995.
- A. Srinivasan, *A Learning Engine for Proposing Hypotheses* (Aleph), 2001.
- D. Angluin, *Learning Regular Sets from Queries and Counterexamples*, Information and Computation 75(2), 1987.
- R. Rivest et R. Schapire, *Inference of Finite Automata Using Homing Sequences*, Information and Computation 103(2), 1993.

Repères de recherche :

- G. Plotkin, *A note on inductive generalization*, Machine Intelligence 5, 1970.
- L. Galarraga et al., *AMIE: Association Rule Mining under Incomplete Evidence in Ontological Knowledge Bases*, VLDB 2013 ; Lajus et al., AMIE 3, 2020.
- R. Evans et E. Grefenstette, *Learning Explanatory Rules from Noisy Data*, JAIR 61, `arXiv:1711.04574`.
- R. Manhaeve et al., *DeepProbLog: Neural Probabilistic Logic Programming*, 2018 ; [LTNtorch](https://github.com/tommasocarraro/LTNtorch), la bibliothèque de logique tensorielle du carnet 07.
- J. Wei et al., *Chain-of-Thought Prompting Elicits Reasoning in Large Language Models*, NeurIPS 2022.
- F. Petersen et al., *Deep Differentiable Logic Gate Networks*, NeurIPS 2022, `arXiv:2210.08277`.
- Pavlov, *Differentiable Logic Synthesis: Spectral Coefficient Selection via Sinkhorn-Constrained Composition*, `arXiv:2601.13953`.
- Smolensky (1990), à l'origine des représentations par produit tensoriel (rôles et fillers, carnet 13).
- McCoy, Soulos, Linzen et Smolensky, *The Emergent Symbolic Structure of Artificial Neural Networks*, `arXiv:2608.29530`.
- Udrescu et al., *AI Feynman 2.0: Pareto-optimal symbolic regression exploiting graph modularity*, NeurIPS 2020, `arXiv:2006.10782`.
- Nair et al., *Solving Mixed Integer Programs Using Neural Networks*, 2021.

---

Voir la licence du dépôt principal. [↑ SymbolicAI](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)

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

## Objectifs d'apprentissage

À l'issue de la série, un lecteur sait faire ce qui suit. Les objectifs sont groupés par nature : les gestes techniques, la méthode qui rend leurs résultats croyables, et les situations où ils s'appliquent.

### Techniques — implémenter, pas seulement reconnaître

1. **Implémenter** l'apprentissage inductif d'un espace d'hypothèses conjonctives — Current-Best-Hypothesis, Candidate Elimination — et lire un espace de versions par ses bornes G et S (carnet 01).
2. **Compiler** un exemple résolu en règle opérationnelle par EBL (expliquer, variabiliser, extraire, simplifier), et **trouver** les attributs déterminants d'un problème par le treillis des déterminations et MINIMAL-CONSISTENT-DET (carnets 02 et 03).
3. **Apprendre** des clauses de Horn récursives par les deux voies de l'ILP : FOIL et son gain en top-down ; résolution inverse, LGG de Plotkin, clause bottom et recherche à la Progol en bottom-up (carnets 04 et 05).
4. **Faire tourner** quatre moteurs ILP réels sur une même tâche et **distinguer** leurs machineries : entailment inverse (Aleph), méta-interprétation (Metagol), contraintes (Popper), descente de gradient (∂ILP) (carnet 06).
5. **Rendre la logique différentiable** — t-normes, prédicats neuronaux, DeepProbLog minimal puis LTNtorch, la satisfaction des formules se lisant dans la perte (carnet 07) — et **discrétiser** un réseau de portes logiques appris par gradient en un circuit booléen (carnet 12).
6. **Extraire** des règles d'un graphe RDF (support, confiance, confiance PCA), les appliquer pour compléter le graphe, et **recouper** la complétion par un chaînage avant Datalog sous clingo (carnet 08).
7. **Apprendre un automate par requêtes** : table d'observation fermée et cohérente, requêtes d'appartenance et d'équivalence, convergence vers l'automate minimal de Myhill-Nerode, puis oracle bruité (carnet 10).
8. **Calculer** le spectre de Walsh-Hadamard exact d'une fonction booléenne, le **distinguer** des poids ternaires d'un PTF, et conduire une recherche discrète bornée contre un oracle exact (carnet 12b).
9. **Proposer des conjectures à un solveur** : fixations de variables pour CP-SAT, détection de leurs conflits, réparation, et mesure du gain par conjecture prise isolément (carnet 15).

### Méthodologiques — ce qui rend le résultat croyable

10. **Concevoir une boucle générateur/oracle** : un LLM propose des règles, un vérificateur formel les accepte ou les rejette, l'erreur retourne au générateur (carnet 09).
11. **Confronter une implémentation artisanale à une référence** : parité de FOIL et de Progol avec clingo et SWI-Prolog, parité des jumeaux C# avec leur carnet Python, et repérage du point où deux implémentations divergent (carnets 04, 05, 06 et leurs jumeaux).
12. **Borner une conclusion de recherche** : distinguer une structure *approximative* d'une structure *exacte* (carnets 13 et 13b), un résultat négatif d'une réfutation (carnet 12c), un gain mesuré sur un budget d'un gain général (carnet 14).
13. **Mesurer contre un contrôle apparié** : null de même effectif pour la sélectivité des atomes, substitution atomique pour la TPR, ablation dirigée pour le dictionnaire creux (carnets 13 et 13b).

### Applicatifs — où le geste sert

14. **Assembler un pipeline neuro-symbolique de bout en bout** — extraction, oracle, graphe, mining, chaînage avant avec provenance, confrontation du LLM seul au graphe raisonné — et **classer les défenses par étage** quand un fait faux entre (carnet 11).
15. **Choisir la méthode selon la contrainte du terrain** : peu d'exemples (EBL, Candidate Elimination), interprétabilité exigée (règles, circuits booléens), connaissance du domaine déjà écrite (déterminations, ontologie).
16. **Retrouver une formule fermée à partir des données** : séparabilité lue dans les gradients d'un réseau, longueur de description en bits, front de Pareto complexité-précision (carnet 14).

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

### Pourquoi cet ordre ?

Sept paliers, et chacun répond à une limite que le précédent a rendue visible. L'ordre n'est pas chronologique ni thématique : il est motivé.

**Palier 1 — l'induction pure (01).** Un agent reçoit des exemples et doit deviner la règle. Candidate Elimination tient l'ensemble entier des hypothèses consistantes ; Current-Best-Hypothesis n'en tient qu'une. Le carnet mesure les deux et expose la limite qui commande la suite : le bruit casse la cohérence, et une disjonction n'entre pas dans une conjonction de contraintes.

**Palier 2 — la connaissance comme accélérateur (02, 03).** Si l'espace d'hypothèses est trop pauvre, on n'élargit pas l'espace : on apporte une théorie du domaine. EBL compile une preuve en règle réutilisable ; RBL cherche les attributs qui déterminent la cible, d'abord par le treillis, ensuite par un test statistique. La comparaison avec l'information mutuelle montre *quand* la connaissance du domaine bat la statistique — et le carnet 02 mesure aussi le cas inverse, où les règles coûtent plus qu'elles ne rapportent.

**Palier 3 — passer des attributs aux programmes (04, 05).** Les carnets 02 et 03 apprennent des *classes* ; un programme logique apprend une *relation récursive*. FOIL descend, la résolution inverse remonte, la clause bottom de Progol borne la recherche. Les deux voies sont écrites de zéro avant d'être confrontées à un moteur.

**Palier 4 — comparer les machineries (06).** Une fois les algorithmes écrits, la question devient « laquelle, quand ? ». Quatre moteurs réels apprennent la même clôture transitive par quatre mécanismes différents, et le carnet rend visibles leurs angles morts : sensibilité à la direction des modes, invention de prédicats, tolérance au bruit. Le ∂ILP différentiable ouvre la porte du palier suivant.

**Palier 5 — différentiable, minier, vérifiable (07, 08, 09, 13, 13b, 15).** La rigidité logique motive de rendre la logique différentiable (07) ; les graphes réels motivent le passage à l'échelle du mining (08) ; l'opacité d'un LLM motive la vérification formelle de ce qu'il propose (09). Deux carnets de recherche sondent le même soupçon par deux lectures concurrentes des mêmes états cachés (13, 13b), et un troisième transporte la boucle générateur/oracle du carnet 09 vers un solveur CP-SAT, où le verdict est plus fin : le mécanisme se transporte, le geste de réparation non (15).

**Palier 6 — apprendre sans échantillon, puis assembler (10, 11, 12, 12b, 12c).** L* renverse le rapport aux données : l'apprenant choisit ses questions et obtient des garanties de minimalité. Le capstone assemble alors les briques des paliers 1 à 5 en un pipeline où chaque étage est un carnet antérieur, et où la leçon vient des sorties réelles : le chaînage avant peut violer les contraintes que l'oracle imposait en amont. Les trois carnets 12 prennent l'autre versant du neuro-symbolique — un circuit discret appris par gradient, son spectre de Fourier exact, et la reproduction bornée d'une revendication de la littérature.

**Palier 7 — changer de question (14).** Tous les paliers précédents apprennent *dans un langage donné* : clauses, règles, circuits, portes. AI Feynman demande si l'on peut retrouver la formule elle-même, et enseigne la leçon transversale de la série : « simple » dépend du langage de description.

Les durées par carnet et le total de la série vivent dans le [catalogue généré](../../../COURSE_CATALOG.generated.md), qui les tient à jour ; les budgets indicatifs ci-dessous sont des ordres de grandeur de lecture, pas des mesures.

### Parcours alternatifs

Quatre entrées dans la série, selon ce que le lecteur vient chercher. Les budgets sont des ordres de grandeur de lecture, les durées mesurées vivant dans le catalogue généré.

- **Parcours rapide** — carnets 01, 07, 09 et 11 (~4 h) : le fil complet en quatre étapes, de l'espace d'hypothèses conjonctives au pipeline où un LLM et un vérificateur se corrigent l'un l'autre. C'est le parcours à conseiller avant une séance de restitution.
- **ILP approfondi** — carnets 01 à 06 (~5 h 30) : les deux voies de l'induction de programmes, puis les quatre moteurs réels. Le lecteur y apprend autant par les algorithmes écrits de zéro que par l'écart mesuré avec Aleph, Popper ou clingo.
- **Théorie des langages** — carnets 01 et 10 (~2 h) : de l'espace d'hypothèses conjonctives à l'automate minimal appris par requêtes, avec la garantie de Myhill-Nerode comme fil.
- **Graphes de connaissances** — carnets 02, 03, 04 et 08 (~3 h 30) : EBL et déterminations, puis clauses de Horn et mining AMIE sur un graphe RDF ; une familiarité avec RDF et SPARQL aide.
- **Neuro-symbolique et recherche** — carnets 07, 09, 13 et 15 (~5 h) : rendre la logique différentiable, faire vérifier les propositions d'un LLM, puis sonder la structure interne d'un réseau et les conjectures qu'il donne à un solveur.

### Séance de restitution

Modalité de la séance : chaque groupe choisit **un exercice** dans la table ci-dessous, le prépare et le présente. Résoudre l'exercice est le minimum attendu ; chaque exercice est assorti d'une **question-twist** — détaillée dans la section « Defi presentation » du carnet correspondant — qui fait partie intégrante de la présentation. Premier arrivé, premier servi : annoncez votre choix pour éviter les doublons. Une soixantaine d'exercices couvrent les quinze carnets ; le nombre exact par carnet vit dans les carnets eux-mêmes.

| # | Notebook | Exercice | Question-twist (en bref) |
|---|----------|----------|--------------------------|
| 1 | [SL-01](SL-01-LogicalLearning-Python.ipynb) | Ex. 1 — CBH avec ordre personnalisé | Deux ordres d'exemples, deux hypothèses finales : pourquoi, à accuracy égale ? |
| 2 | [SL-01](SL-01-LogicalLearning-Python.ipynb) | Ex. 2 — Version Space sur sous-ensemble | Qu'est-ce qui rend un exemple *informatif* (frontières S et G) ? |
| 3 | [SL-01](SL-01-LogicalLearning-Python.ipynb) | Ex. 3 — Règles avec couverture | Compacité vs hypothèse AIMA : quel biais (rasoir d'Occam) préfère l'une à l'autre ? |
| 4 | [SL-01](SL-01-LogicalLearning-Python.ipynb) | Ex. 4 — Réflexion sur le biais conjonctif | Un domaine où ce biais est idéal, un où il est catastrophique (no free lunch) |
| 5 | [SL-01](SL-01-LogicalLearning-Python.ipynb) | Ex. 5 — La consistance sans Occam (aima) | Échantillonner les graines ne prouve pas la minimalité : quel algorithme exact le ferait ? |
| 6 | [SL-02](SL-02-KnowledgeBasedLearning-Python.ipynb) | Ex. 1 — EBL et différenciation symbolique | Exhiber une variabilisation trop agressive qui produit une règle compilée fausse |
| 7 | [SL-02](SL-02-KnowledgeBasedLearning-Python.ipynb) | Ex. 2 — RBL, robustesse au bruit | Une colonne bruitée qui « détermine » accidentellement la cible : régularité accidentelle ou véritable détermination ? |
| 8 | [SL-02](SL-02-KnowledgeBasedLearning-Python.ipynb) | Ex. 3 — Speedup EBL | Le *utility problem* (Minton 1990) : pourquoi apprendre plus finit par ralentir |
| 9 | [SL-03](SL-03-RelevanceLearning-Python.ipynb) | Ex. 1 — Déterminations météo | Une observation bruitée : quelle détermination minimale survit ? |
| 10 | [SL-03](SL-03-RelevanceLearning-Python.ipynb) | Ex. 2 — RBL vs sélection aléatoire | Trouver le point de croisement où la sélection statistique bat le RBL |
| 11 | [SL-03](SL-03-RelevanceLearning-Python.ipynb) | Ex. 3 — Sélecteur hybride | Quelles garanties votre hybride hérite-t-il vraiment ? Contre-exemple construit |
| 12 | [SL-04](SL-04-InductiveLogicProgramming-Python.ipynb) | Ex. 1 — `sibling` avec FOIL | Le rôle du biais de langage : que se passe-t-il sans le littéral `X != Y` ? |
| 13 | [SL-04](SL-04-InductiveLogicProgramming-Python.ipynb) | Ex. 2 — Opérateur W | Généralisation consistante mais fausse : pourquoi le bottom-up y est exposé |
| 14 | [SL-04](SL-04-InductiveLogicProgramming-Python.ipynb) | Ex. 3 — Règles sur mini-KG | Monde clos vs PCA (cf SL-08) : quelle confiance est la bonne pour VOTRE KG ? |
| 15 | [SL-04](SL-04-InductiveLogicProgramming-Python.ipynb) | Ex. 4 — `grandparent` avec Popper | Sans négatif arrière-grand-parent, quel programme plus court devient consistant ? |
| 16 | [SL-05](SL-05-InverseResolution-Python.ipynb) | Ex. 1 — Apprendre `grandmother/2` | Pourquoi `grandparent/2` (sans sexe) est *plus facile* — rôle des négatifs |
| 17 | [SL-05](SL-05-InverseResolution-Python.ipynb) | Ex. 2 — Profondeur de la clause bottom | Croissance de la clause bottom avec la profondeur ; la cible reste-t-elle dans le treillis ? |
| 18 | [SL-05](SL-05-InverseResolution-Python.ipynb) | Ex. 3 — Tolérance au bruit | Le score `p - n - L` comme argument MDL : quand préfère-t-il une clause imparfaite ? |
| 19 | [SL-05](SL-05-InverseResolution-Python.ipynb) | Ex. 4 — Réduction de Plotkin | Subsomption vs implication : le cas des clauses récursives ou elles divergent |
| 20 | [SL-05](SL-05-InverseResolution-Python.ipynb) | Ex. 5 — Aleph face au bruit | Mémoriser l'exception, sur-généraliser ou payer L dans f : trois frontières face au même bruit |
| 21 | [SL-06](SL-06-ModernILP-Python.ipynb) | Ex. 1 — Direction de mode (Aleph) | Pourquoi `(+,-)` apprend et `(+,+)` échoue : ce que la direction des modes change pour l'entailment inverse |
| 22 | [SL-06](SL-06-ModernILP-Python.ipynb) | Ex. 2 — `grandparent` non récursif | Cible à 2 sauts sans clôture : quel biais (max_clauses, pas de récursion) suffit, et l'invention de prédicats sert-elle encore ? |
| 23 | [SL-06](SL-06-ModernILP-Python.ipynb) | Ex. 3 — Robustesse au bruit (∂ILP vs symbolique) | Un faux positif injecté : ∂ILP dégrade sa confiance, Popper exact n'a pas de notion de bruit — à quel prix chacun ? |
| 24 | [SL-07](SL-07-NeuroSymbolic-Python.ipynb) | Ex. 2 — LTN frère/oncle | Retirer les axiomes négatifs : pourquoi une LTN a besoin de négatifs explicites |
| 25 | [SL-07](SL-07-NeuroSymbolic-Python.ipynb) | Ex. 3 — Règle transitive `ancestor` | Le modèle trivial « vrai partout » sature la règle : qu'est-ce qui l'évite ? |
| 26 | [SL-07](SL-07-NeuroSymbolic-Python.ipynb) | Ex. 4 — T-norm de Lukasiewicz | Gradients exactement nuls : qu'est-ce qu'une sémantique floue *apprenable* ? |
| 27 | [SL-07](SL-07-NeuroSymbolic-Python.ipynb) | Ex. 5 — Ablation de l'axiome 4 (LTNtorch) | Le négatif difficile (Marie, Pierre) est-il indispensable ? Contraste avec clingo (SL-08) |
| 28 | [SL-08](SL-08-KnowledgeGraphs-ILP-Python.ipynb) | Ex. 1 — Nouvelle relation au KG | Règles redondantes (même extension, syntaxe différente) : comment AMIE les évite |
| 29 | [SL-08](SL-08-KnowledgeGraphs-ILP-Python.ipynb) | Ex. 2 — PCA confidence | Construire un mini-KG où la PCA confidence est trompeuse |
| 30 | [SL-08](SL-08-KnowledgeGraphs-ILP-Python.ipynb) | Ex. 3 — Règles à 3 atomes | Explosion combinatoire : pourquoi AMIE impose des règles fermées, à quel prix |
| 31 | [SL-08](SL-08-KnowledgeGraphs-ILP-Python.ipynb) | Ex. 4 — Réparation minimale (clingo) | Les réparations optimales sont ex æquo : départager par des poids de confiance |
| 32 | [SL-09](SL-09-LLM-SymbolicLearning-Python.ipynb) | Ex. 1 — Prompt personnalisé | Changer de modèle LLM : que garantit vraiment l'oracle symbolique ? |
| 33 | [SL-09](SL-09-LLM-SymbolicLearning-Python.ipynb) | Ex. 2 — Prompt direct vs CoT | Validation oracle vs plausibilité du texte : les deux métriques peuvent diverger |
| 34 | [SL-09](SL-09-LLM-SymbolicLearning-Python.ipynb) | Ex. 3 — Détection d'hallucinations | Le détecteur suppose un monde clos : que devient-il en monde ouvert (cf SL-08) ? |
| 35 | [SL-09](SL-09-LLM-SymbolicLearning-Python.ipynb) | Ex. 4 — Taux d'hallucination du vrai LLM | Maximiser le taux de validation ou le nombre de règles validées par appel ? |
| 36 | [SL-10](SL-10-ActiveAutomataLearning-Python.ipynb) | Ex. 1 — Le langage « contient abb » | Certificat de minimalité : un suffixe distinguant pour chaque paire d'états (Myhill-Nerode) |
| 37 | [SL-10](SL-10-ActiveAutomataLearning-Python.ipynb) | Ex. 2 — Fiabilité de l'EQ échantillonnée | Relier le taux de réussite empirique à la borne PAC ; construire une distribution adverse |
| 38 | [SL-10](SL-10-ActiveAutomataLearning-Python.ipynb) | Ex. 3 — Contre-exemples : préfixes vs suffixes | Le pire cas qui fait exploser la table d'observation (Rivest-Schapire) |
| 39 | [SL-10](SL-10-ActiveAutomataLearning-Python.ipynb) | Ex. 4 — Oracle bruité | Réparer L* par vote majoritaire : surcoût en requêtes et probabilité résiduelle d'erreur |
| 40 | [SL-11](SL-11-Capstone-NeuroSymbolic-Python.ipynb) | Ex. 1 — Étendre le schéma (`marie_avec`) | Le mineur redécouvre la symétrie injectée par l'oracle : règle ou tautologie ? |
| 41 | [SL-11](SL-11-Capstone-NeuroSymbolic-Python.ipynb) | Ex. 2 — Politique de conflit à sources | *Truth discovery* : estimer la fiabilité des sources en même temps que les faits |
| 42 | [SL-11](SL-11-Capstone-NeuroSymbolic-Python.ipynb) | Ex. 3 — Le bon seuil n'existe pas | Vraie et fausse règle à confiance égale (0.67) : quel signal au-delà du seuil ? |
| 43 | [SL-11](SL-11-Capstone-NeuroSymbolic-Python.ipynb) | Ex. 4 — Empoisonnement bout-en-bout | Classer les défenses par étage du pipeline ; où s'arrête la provenance ? |
| 44 | [SL-12](SL-12-DifferentiableLogicGateNetworks-Python.ipynb) | Ex. 1 — Variation de profondeur | Trade-off capacité vs sur-apprentissage : combien de couches pour quel régime ? |
| 45 | [SL-12](SL-12-DifferentiableLogicGateNetworks-Python.ipynb) | Ex. 2 — Porte favorite d'un neurone isolé | Quelle porte (AND/NAND/XOR) l'apprentissage favorise-t-il pour MNIST ? |
| 46 | [SL-12](SL-12-DifferentiableLogicGateNetworks-Python.ipynb) | Ex. 3 — Robustesse au bruit pixel | La discrétisation booléenne aide-t-elle face au bruit vs un MLP équivalent ? |
| 47 | [SL-01b](SL-01b-LogicalLearning-Lean.ipynb) | Ex. 1 — Erreur nulle contre soi-même (Lean) | Spécialiser `trueError_self` : quel quantificateur la structure `Distribution` rend-il gratuit ? |
| 48 | [SL-01b](SL-01b-LogicalLearning-Lean.ipynb) | Ex. 2 — Masse des échantillons (Lean) | `sampleWeight_sum_one` : pourquoi la Fubini discrète suffit-elle sans théorie de la mesure ? |
| 49 | [SL-01b](SL-01b-LogicalLearning-Lean.ipynb) | Ex. 3 — Symétrie du désaccord (Lean) | `trueError_comm` : que dit la symétrie sur l'interprétabilité de l'erreur comme distance ? |
| 50 | [SL-12b](SL-12b-SpectralLogicSynthesis-Python.ipynb) | Ex. 1 — Spectre de EXACT2 (poids de Hamming) | Degré Fourier contre degré PTF : lequel ment sur la complexité ? |
| 51 | [SL-12b](SL-12b-SpectralLogicSynthesis-Python.ipynb) | Ex. 2 — Sinkhorn sur ligne uniforme | Une permutation unique au coût minimal prouve-t-elle que le routage « a choisi » ? |
| 52 | [SL-12b](SL-12b-SpectralLogicSynthesis-Python.ipynb) | Ex. 3 — Instance séparant SA et PT | Qu'est-ce qui rend une instance « dure » pour une seule température ? |
| 53 | [SL-13](SL-13-Discover-TPR-Python.ipynb) | Ex. 1 — Tâche à rôles sémantiques (argmax_pos) | Quand les rôles ne sont plus des positions mais des étiquettes, la TPR émerge-t-elle encore ? |
| 54 | [SL-13](SL-13-Discover-TPR-Python.ipynb) | Ex. 2 — Constituent surgery sémantique | La permutation des rôles 0↔1 dans la TPR produit-elle la sortie attendue pour la séquence aux rôles permutés ? |
| 55 | [SL-13](SL-13-Discover-TPR-Python.ipynb) | Ex. 3 — Seuil de capacité et TPR | Quel d_model marque le point d'inflexion entre compression forcée et TPR non-nécessaire ? |
| 56 | [SL-14](SL-14-AIFeynman-Discover-Equations-Python.ipynb) | Ex. 1 — Rejet statistique anticipé (ν=10) | En combien de points un mauvais candidat meurt-il, et pourquoi ν=10 rend-il le test quasi immunisé aux faux positifs ? |
| 57 | [SL-14](SL-14-AIFeynman-Discover-Equations-Python.ipynb) | Ex. 2 — Addition relativiste récursive | La symétrie généralisée se déclenche deux fois de suite : jusqu'où peut-on empiler les vitesses ? |
| 58 | [SL-14](SL-14-AIFeynman-Discover-Equations-Python.ipynb) | Ex. 3 — Frontière de bruit | À quel niveau de bruit la forme relativiste disparaît-elle du front — et que mesure vraiment la table 3 du papier ? |
| 59 | [SL-15](SL-15-LearnedConjectures-Solver-Python.ipynb) | Ex. 1 — Top-k par confiance | Le hint complet ne rend que −18 % là où une fixation isolée vaut −62 % : quelle tête garder, et pourquoi la confiance du MLP n'est *pas* le juge du gain ? |
| 60 | [SL-15](SL-15-LearnedConjectures-Solver-Python.ipynb) | Ex. 2 — Réfutation des conjectures | Détecter les arêtes en conflit : comment une conjecture peut-elle être *fausse* au sens de l'oracle et pourtant *profitable* au solveur ? |
| 61 | [SL-15](SL-15-LearnedConjectures-Solver-Python.ipynb) | Ex. 3 — Réparation gloutonne | Retirer les fixations conflictuelles jusqu'à zéro conflit : le hint réparé conserve-t-il le gain, ou paie-t-il le coût de sa réparation ? |

Note : dans SL-07, le premier exercice de la numérotation interne est un exemple guide ; les exercices à piocher sont Ex. 2 à Ex. 5.

## Contenu détaillé des carnets

Ce que chaque carnet contient, dans l'ordre où il le présente. Les intitulés sont ceux des sections du carnet lui-même ; les objectifs, les exercices et le défi de présentation ne sont pas repris ici, ils vivent dans le carnet.

### 01 — Apprentissage logique : CBH Search et Version Space

Le carnet enchaîne : le problème du restaurant d'AIMA ; la représentation des hypothèses et la consistance ; la généralisation et la spécialisation ; l'algorithme Current-Best-Hypothesis ; l'algorithme Version Space par Candidate Elimination ; la prédiction avec le Version Space ; la visualisation de son évolution ; les limites du cadre conjonctif ; l'implémentation de référence aima-python. Le jumeau C# suit les mêmes sections écrites à la main, et ajoute la comparaison CBH contre Version Space ainsi qu'un pont PythonNet vers `aima-python`.

### 01b — Apprentissage PAC formellement (Lean)

Le vocabulaire PAC (distribution, hypothèse, erreur vraie) ; l'échantillon, les tirages i.i.d. et le poids d'un échantillon ; la borne de généralisation d'une classe finie ; le cadre agnostique ; la concentration, de Markov à Hoeffding ; le perceptron, convergence de Novikoff et serrage de la borne ; la lecture du fil ; la théorie effective de la représentation (arc `EffectiveTheory`) ; la théorie mathématique de l'univers (structures, générateurs, renommage). Tout s'exécute en noyau Lean sur le lake `learning_theory_lean`.

### 02 — Apprentissage et connaissance (EBL & RBL)

Le carnet avance : le cadre général de la connaissance dans l'apprentissage ; l'idée d'EBL ; l'exemple de la simplification arithmétique ; la variabilisation et l'extraction de règle ; l'implémentation complète ; l'efficacité et l'opérationnalité ; l'introduction aux déterminations par RBL ; la synthèse. Le jumeau C# part des quatre contraintes d'apprentissage, déroule EBL par chaînage avant avec unification, mesure le gain, puis vérifie une détermination.

### 03 — Apprentissage basé sur la pertinence

Pourquoi la pertinence ; les déterminations, formalisme et propriétés ; le treillis des déterminations ; l'algorithme MINIMAL-CONSISTENT-DET ; la sélection d'attributs guidée par la connaissance ; les déterminations et la sémantique web. Le jumeau C# ajoute le cas de l'activité biologique des molécules, la borne PAC comme avantage quantifié, le parallèle avec OWL, l'information mutuelle, puis confronte le classement à l'importance des variables mesurée par ML.NET.

### 04 — Programmation logique inductive

Pourquoi l'ILP ; les clauses de Horn et l'unification ; FOIL, l'apprentissage top-down ; la résolution inverse, bottom-up ; une application complète de FOIL pas à pas ; l'ILP et les graphes de connaissances ; puis le moteur Popper. Le jumeau C# détaille les briques de FOIL, le problème des ancêtres, l'évaluation des clauses candidates, la couverture séquentielle et un ILP sur mini graphe de connaissances, avec un pont vers clingo.

### 05 — Résolution inverse et Progol

Inverser la déduction ; la représentation et la couverture ; la généralisation la moins générale de Plotkin ; la θ-subsomption comme ordre du treillis ; l'entailment inverse et la clause bottom ; la recherche à la Progol ; de Progol aux systèmes modernes ; puis Aleph. Le jumeau C# reprend ces étapes jusqu'à la recherche Progol, apprend `grandmother/2` et vérifie la parité avec SWI-Prolog.

### 06 — Moteurs ILP modernes

Quatre paradigmes pour une seule tâche : Aleph et l'entailment inverse, Metagol et l'apprentissage méta-interprétatif, Popper et la recherche par contraintes, ∂ILP et la descente de gradient ; puis la synthèse qui les compare. Le jumeau C# réécrit le noyau de FOIL, l'applique à `ancestor/2`, le vérifie par la couverture, le mesure sur un graphe qui grandit, puis se prononce sur la portabilité des quatre moteurs.

### 07 — Intégration neuro-symbolique

Pourquoi combiner neural et symbolique ; les opérateurs logiques différentiables ; les prédicats neuronaux ; une logique tensorielle simplifiée ; le raisonnement guidé par la logique ; un DeepProbLog simplifié ; la vraie bibliothèque LTNtorch ; la comparaison des approches neuro-symboliques.

### 08 — ILP moderne et knowledge graphs

L'ILP sur données structurées ; la construction d'un graphe avec rdflib ; l'extraction des données pour le mining ; la découverte de règles de Horn ; l'énumération des candidats ; le passage des règles d'association aux règles logiques ; la complétion du graphe ; la visualisation ; les propriétés logiques et leur composition ; la comparaison entre ILP classique et rule mining ; puis le chaînage avant sous clingo. Le jumeau C# construit le même graphe avec dotNetRDF et s'arrête à la limite honnête de son périmètre pour l'ASP.

### 09 — LLMs et apprentissage symbolique

Les LLM comme moteurs de raisonnement symbolique ; le LLM comme générateur d'hypothèses ; la vérification symbolique de ses sorties ; le raisonnement pas à pas comme explication ; le pipeline complet des exemples aux règles validées ; l'itération et le raffinement ; la robustesse du générateur et le raccord à l'écosystème.

### 10 — Apprentissage actif d'automates

Du passif à l'actif, le modèle MAT ; la table d'observation ; l'algorithme L* ; son exécution complète sur le langage cible ; les garanties de minimalité et de complexité ; l'oracle d'équivalence en pratique ; puis un pont vers Infer.NET, et en annexe la postérité du domaine. Le jumeau C# suit le même plan avec la seule bibliothèque standard de .NET.

### 11 — Capstone neuro-symbolique

Le pipeline ; le corpus et le schéma ; l'extraction par LLM ; l'oracle symbolique ; le graphe de connaissances ; le mining de règles à la manière d'AMIE ; le chaînage avant et ce qu'il découvre ; puis la boucle bouclée où le LLM seul est confronté au graphe raisonné.

### 12 — Portes logiques différentiables

La motivation et le contexte historique ; le modèle difflogic ; l'apprentissage sur MNIST en 20 × 20 pixels ; l'inspection des prédictions ; l'inférence rapide par `CompiledLogicNet`, présentée comme avancée et bornée à une machine qui sait la compiler.

### 12b — Synthèse logique spectrale

La convention booléenne, écrite une seule fois ; les caractères de Walsh et la transformée exacte ; les coefficients de Fourier exacts contre les poids ternaires ; le routage par Sinkhorn ; la quantification puis la recherche discrète, par MCMC et parallel tempering ; le pont avec les portes locales du carnet 12. Le jumeau C# reprend les mêmes sections et ajoute un « Vérifiez votre compréhension ».

### 12c — Reproduire Pavlov

Le carnet mène la reproduction en deux phases et conclut sur le gain mesuré du routage par Sinkhorn ; ses cellules de mesure se suivent sans titre intermédiaire, ce qui explique le petit nombre de sections.

### 13 et 13b — Structure TPR, deux lectures des états cachés

Le carnet 13 ouvre sur son plan, ses prérequis et sa portée déclarée, puis enchaîne les mesures jusqu'à la conclusion, sans titres intermédiaires entre les cellules. Le carnet 13b suit la même forme pour relire les mêmes états cachés avec un dictionnaire creux.

### 14 — AI Feynman

Chercher dans l'espace des formules ; lancer la recherche avec `run_aifeynman` ; le cœur de l'algorithme, les symétries lues dans les gradients ; MEDL, décrire plutôt que minimiser ; et la leçon finale, « simple » dépend du langage de description.

### 15 — Conjectures apprises pour un vérificateur

Le cadre, conjecture, oracle, réfutation ; l'apprenant qui imite les solutions sœurs ; la conjecture individuelle et la décomposition du hint ; les conjectures de tête, en top-k ; la conjecture projetée, où l'oracle répare l'apprenant ; la boucle complète, exécutée ; une deuxième famille, la couverture d'ensemble ; et la synthèse qui ramène la conjecture au statut d'hypothèse réfutable.

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
- **Les carnets 04 et 06 échouent sous Windows** : Aleph et Popper passent par SWI-Prolog et par `SIGALRM` pour leur délai de garde, tous deux absents d'un noyau Windows natif. Il faut le noyau `python3-wsl` (voir Noyaux Jupyter) ; un moteur introuvable est signalé par son drapeau `HAS_*` et le carnet poursuit sans lui.
- **Le carnet 14 échoue hors de son conteneur** : le paquet `aifeynman` figé en 2021 importe `numpy.distutils`, retiré de NumPy 2. Lancez-le par papermill dans l'image `aifeynman:sl14-py313` plutôt que dans l'environnement de la flotte.

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
| [Tweety](../Tweety/README.md) | Les logiques formelles que les carnets 04 et 05 écrivent à la main (clauses de Horn, unification) : Tweety les raisonne comme des théories données, la série les apprend des exemples. |
| [SemanticWeb](../SemanticWeb/README.md) | RDFS et OWL formalisent les déterminations et les hiérarchies de généralité ; SW-02 donne les bases RDF utiles au carnet 08. |
| [Planners](../Planners/README.md) | L'heuristique opérationnelle qu'EBL compile (carnet 02) répond au problème des heuristiques de planification : rendre une règle utilisable sans la redériver à chaque appel. |
| [Lean](../Lean/README.md) · [ML](../../ML/README.md) | Le lake `learning_theory_lean`, hébergé par la série ML, est exécuté par le carnet 01b ; l'arbre de preuve d'EBL (carnet 02) a la forme d'un but de preuve Lean, avec la même décomposition en sous-buts. |
| [Search](../../Search/README.md) | Le benchmark agrégé des conjectures apprises vit dans App-33 ; la série porte aussi solveurs et métaheuristiques. |
| [Probas](../../Probas/README.md) · [GameTheory](../../GameTheory/README.md) | Le capstone (carnet 11) raisonne sur des faits tenus pour certains ; Probas (Infer.NET) et GameTheory outillent le cas où les faits sont incertains ou dépendent de la décision d'un autre agent. |
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

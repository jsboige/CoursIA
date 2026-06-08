# SymbolicLearning - Apprentissage Symbolique

<!-- CATALOG-STATUS
series: SymbolicAI-SymbolicLearning
pedagogical_count: 7
breakdown: SymbolicLearning=7
maturity: PRODUCTION=7
-->

Comment un agent peut-il apprendre a partir de connaissances existantes plutot que de donnees brutes ? Cette serie explore l'apprentissage symbolique tel que decrit dans le chapitre 19 d'AIMA (Russell & Norvig), depuis l'apprentissage inductif pur (CBH, Version Space) jusqu'aux methodes guidees par la connaissance (EBL, RBL).

Le premier notebook pose les bases : representation d'hypotheses comme conjonctions de contraintes, algorithmes Current-Best-Hypothesis et Candidate Elimination (Version Space), et leurs limites face au bruit et aux concepts disjonctifs. Le second notebook montre comment la connaissance du domaine accelere l'apprentissage : l'apprentissage base sur les explications (EBL) compile les theories en heuristiques operationnelles, et l'apprentissage base sur la pertinence (RBL) identifie les attributs determinant via les determinations. Le troisieme notebook approfondit le RBL avec le treillis des determinations, l'algorithme MINIMAL-CONSISTENT-DET et une comparaison avec sklearn. Le quatrieme notebook couvre la programmation logique inductive (ILP) : l'algorithme FOIL (top-down), la resolution inverse (bottom-up) et la connexion avec les knowledge graphs. Les trois derniers notebooks ouvrent vers des methodes contemporaines : SL-5 introduit le neuro-symbolique (T-norms differentiables, Logic Tensor Networks, DeepProbLog) ; SL-6 outille la decouverte de regles sur knowledge graphs reels avec rdflib et AMIE rule mining ; SL-7 boucle LLM et verification symbolique pour fiabiliser le raisonnement formel guide par modeles de langage.

**A qui s'adresse cette serie** : etudiants en IA, informaticiens interesses par le raisonnement symbolique, et chercheurs en apprentissage automatique souhaitant comprendre les approches non-statistiques. Les notebooks (~6h total) ne necessitent que Python 3.10+ standard library, sauf SL-3 (scikit-learn + numpy pour la comparaison RBL / information mutuelle) et SL-6 (rdflib pour les knowledge graphs). Une familiarite avec la logique propositionnelle suffit pour SL-1 a SL-4 ; SL-5 et SL-7 supposent une intuition des reseaux de neurones et des LLMs respectivement. Ils constituent un complement theorique aux series [Tweety](../Tweety/README.md) (argumentation computationnelle), [SemanticWeb](../SemanticWeb/README.md) (representation de connaissances) et [ML](../../ML/README.md) (apprentissage statistique - contraste avec l'inductif symbolique).

## Pourquoi cette serie

L'apprentissage symbolique represente la contrepartie theorique du machine learning statistique. Tandis que les methodes modernes (deep learning, ensembles d'arbres) excellent a extraire des patterns de grandes masses de donnees, elles souffrent de trois limites fondamentales que l'approche symbolique adresse directement :

- **Peu de donnees disponibles** : les methodes symboliques comme Candidate Elimination ou FOIL apprennent a partir de quelques exemples,voire d'un seul (EBL). Quand la collecte de donnees est couteuse ou impossible (diagnostic medical rare, validation formelle), l'induction pure ne fonctionne pas.
- **Interpretabilité requise** : une regle logique `IF temperature > 38 AND toux THEN infection` est comprehensible par un humain. Un reseau de neurones de 100M de parametres ne l'est pas. Pour les applications critique ou reglementees (medecine, finance, justice), l'interpretabilité n'est pas un luxe — c'est une exigence.
- **Integration avec la connaissance existante** : les methodes symboliques combinent examples ET theorie du domaine. EBL compile un exemple prouve en une regle operationnelle generale ; RBL identifie les attributs determinant via des contraintes formelles. Aucune methode statistique ne peut exploiter cette connaissance a priori de la meme facon.

Cette serie montre que les deux approches ne s'opposent pas — elles se **complementent**. La phase finale (SL-5 a SL-7) explore explicitement cette integration : T-norms differentiables pour rendre la logique compatible avec l'entrainement neuronal, rule mining sur knowledge graphs reels, et boucles de verification symbolique pour fiabiliser les sorties LLM.

## Objectifs d'apprentissage

A l'issue de cette serie, vous serez capable de :

1. **Implémenter** les algorithmes d'apprentissage inductif de base (CBH, Candidate Elimination, Version Space)
2. **Compiler** des preuves en heuristiques operationnelles via EBL, et **identifier** les attributs pertinents via RBL et les determinations
3. **Construire** le treillis des determinations et appliquer MINIMAL-CONSISTENT-DET pour la selection guidee d'attributs
4. **Apprendre** des regles logiques ( clauses Horn ) a partir d'exemples avec FOIL et la resolution inverse
5. **Intégrer** logique et apprentissage neuronal via T-norms, Logique Tensorielle, et DeepProbLog
6. **Extraire** des regles de knowledge graphs reels avec rdflib et AMIE, et **effectuer** la completion de graphes
7. **Concevoir** une boucle LLM-symbolique : extraction de regles IF-THEN depuis du texte, verification de coherence formelle, feedback pour l'amelioration

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 7 |
| Kernel | Python 3 |
| Duree estimee | ~370 min |
| prerequis | Python 3.10+ (standard library + sklearn pour SL-3/SL-4, rdflib pour SL-6) |

## Parcours d'apprentissage

### Phase 1 : Fondations inductives (SL-1, ~50 min)

Le parcours commence par l'apprentissage inductif pur : un agent doit decouvrir une regle cachee a partir d'exemples. SL-1 presente les algorithmes fondamentaux — Current-Best-Hypothesis (ajuste une seule hypothese incrementalement) et Candidate Elimination (maintient l'ensemble complet des hypotheses consistantes, le "Version Space"). Vous experimentez leurs limites face au bruit et aux concepts disjonctifs, ce qui motive naturellement les approches plus riches introduites ensuite.

### Phase 2 : Apprentissage base sur la connaissance (SL-2 a SL-3, ~105 min)

La deuxieme phase introduit l'idee centrale que **la connaissance accelere l'apprentissage**. EBL (SL-2) montre comment compiler un exemple prouve en une regle operationnelle generale, en quatre etapes : expliquer, variabiliser, extraire, simplifier. RBL (SL-2 + SL-3) explore une autre facette : identifier les attributs qui determinant vraiment la cible via le formalisme des determinations et le treillis des sous-ensembles d'attributs. La comparaison avec sklearn (information mutuelle) montre quand la connaissance du domaine bat la statistique brute.

### Phase 3 : Programmation logique inductive (SL-4, ~55 min)

SL-4 fait le pont entre apprentissage automatique et intelligence artificielle symbolique classique en couvrant l'ILP : apprentissage de programmes logiques (clauses Horn) a partir d'exemples. L'algorithme FOIL (top-down) et la resolution inverse (bottom-up) sont implémentes de zero, puis appliques aux knowledge graphs — avec extraction de regles AMIE et requetes SPARQL CONSTRUCT.

### Phase 4 : Integration neuro-symbolique (SL-5 a SL-7, ~160 min)

La phase finale explore les methodes contemporaines a l'intersection du symbolique et du connexionniste. SL-5 introduit les T-norms differentiables, les predicats neuronaux et les Logics Tensor Networks qui rendent la logique operationnelle dans un gradient descent. SL-6 passe a l'echelle avec le rule mining reel sur des knowledge graphs construits avec rdflib (AMIE, completion de graphes). SL-7 ferme la boucle avec LLMs : extraction de regles depuis du texte naturel, verification symbolique des sorties, et boucles de retroaction pour fiabiliser le raisonnement.

### Parcours alternatives

#### Parcours rapide (SL-1 + SL-5 + SL-7, ~2h)

Pour ceux qui veulent saisir l'essence sans suivre toute la progression : les fondements inductifs (SL-1), l'integration neuro-symbolique (SL-5), et la verification LLM (SL-7). Donne une vue d'ensemble du spectre, de l'inductif pur au LLM symbolique.

#### Parcours ILP approfondi (SL-1 a SL-4, ~265 min)

Pour les etudiants en logique et IA symbolique : suivre les quatre premiers notebooks dans l'ordre pour maitriser l'apprentissage inductif complet — de Candidate Elimination a FOIL, resolution inverse, et rule mining sur KG.

#### Parcours knowledge graphs (SL-2, SL-3, SL-4, SL-6, ~220 min)

Pour les professionnels du web semantique et des donnees structurees : EBL, RBL, FOIL sur clauses Horn, puis application directe sur des knowledge graphs reels avec rdflib et AMIE. Presuppose une familiarite avec RDF/SPARQL.

## Notebooks

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 1 | [SL-1 - Apprentissage Logique](SL-1-LogicalLearning.ipynb) | CBH, Version Space, Candidate Elimination | 50 min |
| 2 | [SL-2 - Apprentissage et Connaissance](SL-2-KnowledgeBasedLearning.ipynb) | EBL, RBL, determinations | 55 min |
| 3 | [SL-3 - Apprentissage Base sur la Pertinence](SL-3-RelevanceLearning.ipynb) | Treillis des determinations, MINIMAL-CONSISTENT-DET, RBL vs sklearn | 50 min |
| 4 | [SL-4 - Programmation Logique Inductive](SL-4-InductiveLogicProgramming.ipynb) | FOIL, resolution inverse, clauses Horn, knowledge graphs | 55 min |
| 5 | [SL-5 - Integration Neuro-Symbolique](SL-5-NeuroSymbolic.ipynb) | T-norms, predicats neuronaux, LTN, DeepProbLog | 55 min |
| 6 | [SL-6 - ILP Moderne et Knowledge Graphs](SL-6-KnowledgeGraphs-ILP.ipynb) | rdflib, AMIE rule mining, completion KG | 55 min |
| 7 | [SL-7 - LLMs et Apprentissage Symbolique](SL-7-LLM-SymbolicLearning.ipynb) | Prompting, extraction de regles, verification symbolique | 50 min |

## Contenu detaille

### SL-1-LogicalLearning.ipynb

| Section | Contenu |
|---------|---------|
| Domaine restaurant | Attributs, exemples AIMA, hypotheses comme conjonctions |
| Consistance | Faux positifs/negatifs, verification d'hypotheses |
| Generalisation/Specialisation | Operations fondamentales, hierarchie de generalite |
| CBH | Algorithme Current-Best-Hypothesis (AIMA Fig 19.2) |
| Version Space | Candidate Elimination, G-set et S-set (AIMA Fig 19.3) |
| Prediction | Strategies unanime, conservateur, majority |
| Limites | Sensibilite au bruit, incapacite a representer les disjonctions |

### SL-2-KnowledgeBasedLearning.ipynb

| Section | Contenu |
|---------|---------|
| Cadre general | Contrainte d'entrainement, EBL vs RBL vs KBIL |
| EBL - Principe | Exemple de Zog, 4 etapes (expliquer, variabiliser, extraire, simplifier) |
| EBL - Arithmetique | Simplification d'expressions, arbre de preuve |
| EBL - Implementation | Classe ArithmeticEBL complete |
| EBL - Efficacite | Operationalite vs generalite, proliferation de regles |
| RBL - Determinations | Verification fonctionnelle, reduction d'espace |
| RBL - MINIMAL-CONSISTENT-DET | Algorithme AIMA 19.4 |
| RBL - Impact quantitatif | Reduction exponentielle de l'espace des hypotheses |

### SL-3-RelevanceLearning.ipynb

| Section | Contenu |
|---------|---------|
| Determinations | Formalisme, monotonie, minimalite, `check_determination()` |
| Treillis des determinations | `build_determination_lattice()`, visualisation ASCII, up-set |
| MINIMAL-CONSISTENT-DET | Implementation detaillee, donnees moleculaires |
| Selection guidee | RBL vs sklearn (information mutuelle), comparaison |
| Analyse PAC | Reduction exponentielle, bornes d'echantillonnage |
| Web Semantique | Parallel RBL <-> OWL (FunctionalProperty, hasKey) |

### SL-4-InductiveLogicProgramming.ipynb

| Section | Contenu |
|---------|---------|
| Clauses Horn | Representation, `Literal`, `HornClause`, unification |
| FOIL | Algorithme top-down, gain FOIL, litteraux candidats |
| FOIL pas-a-pas | Trace detaillee sur le probleme ancestor |
| Resolution inverse | Operateurs V (absorption) et W (identification) |
| Knowledge Graphs | Regles AMIE, triples RDF, SPARQL CONSTRUCT |
| Exercices | sibling, operateur W, regles sur KG |

### SL-5-NeuroSymbolic.ipynb

| Section | Contenu |
|---------|---------|
| T-norms / T-conorms | Operateurs logiques differentiables |
| Predicats neuronaux | Fonctions P(x) -> [0,1] apprises |
| LTN | Logique Tensorielle simplifiee |
| Raisonnement guide | Regles logiques guidant l'entrainement neuronal |
| DeepProbLog | Programmation logique probabiliste + predicats neuronaux |

### SL-6-KnowledgeGraphs-ILP.ipynb

| Section | Contenu |
|---------|---------|
| Knowledge Graphs | Construction avec rdflib |
| AMIE rule mining | Decouverte de regles de Horn sur KG |
| Completion | Inference de nouveaux triples |

### SL-7-LLM-SymbolicLearning.ipynb

| Section | Contenu |
|---------|---------|
| LLMs et raisonnement | Forces et limites pour le raisonnement symbolique |
| Parseur de regles | Extraction de regles IF-THEN depuis du texte |
| Verification symbolique | Coherence formelle des sorties LLM |
| Boucle LLM-Symbolique | Generation + verification + feedback |

## Concepts cles

| Concept | Explication | Notebook |
|---------|-------------|----------|
| **Hypothese FOL** | Conjonction de contraintes sur les attributs | SL-1 |
| **Version Space** | Ensemble de toutes les hypotheses consistantes | SL-1 |
| **CBH** | Maintient une seule hypothese ajustee incrementalement | SL-1 |
| **EBL** | Extrait une regle generale d'un seul exemple par deduction | SL-2 |
| **RBL** | Identifie les attributs pertinents via les determinations | SL-2 |
| **Determination** | Relation fonctionnelle entre attributs | SL-2, SL-3 |
| **KBIL** | Apprentissage inductif guide par la connaissance | SL-2 |
| **Treillis des determinations** | Ensemble partiellement ordonne des sous-ensembles d'attributs | SL-3 |
| **MINIMAL-CONSISTENT-DET** | Trouve la determination minimale par taille croissante | SL-3 |
| **FOIL** | Apprentissage top-down de clauses Horn | SL-4 |
| **Resolution inverse** | Apprentissage bottom-up par operateurs V et W | SL-4 |
| **Clause Horn** | Regle logique avec au plus un litteral positif | SL-4 |
| **Unification** | Trouve une substitution rendant deux termes egaux | SL-4 |
| **ILP** | Apprentissage de programmes logiques a partir d'exemples | SL-4 |
| **T-norm** | Generalisation differentiable de AND | SL-5 |
| **DeepProbLog** | Programmation logique probabiliste + predicats neuronaux | SL-5 |
| **Knowledge Graph** | Graphe oriente de triples (sujet, predicat, objet) | SL-6 |
| **AMIE** | Rule mining sur knowledge graphs incomplets | SL-6 |
| **LLM-Symbolique** | Boucle de retroaction LLM + verification formelle | SL-7 |

## prerequis

### Connaissances requises

- Python de base (fonctions, classes, tuples, dictionnaires)
- Logique propositionnelle (conjonctions, predicats)
- Notions d'apprentissage supervisé (classification binaire)

### Environnement Python

Aucune dependance externe pour SL-1 et SL-2 (bibliothèque standard Python 3.10+ uniquement). SL-3 utilise `scikit-learn` et `numpy` pour la comparaison avec la selection statistique. SL-4 utilise uniquement la bibliotheque standard. SL-5 utilise uniquement la bibliotheque standard. SL-6 utilise `rdflib`. SL-7 utilise uniquement la bibliotheque standard.

## FAQ / Troubleshooting

### `rdflib` ne s'installe pas ou plantage a l'execution

SL-6 depend de `rdflib` pour manipuler les knowledge graphs RDF. Si l'installation echoue :

```bash
pip install rdflib
```

Si rdflib plante avec une erreur de compilateur C sur les parsers RDF/XML : installez `lxml` comme fallback `pip install lxml`, ou utilisez un environnement conda (`conda install -c conda-forge rdflib`).

### JPype / Java : erreurs courantes avec les bindings

Certains algorithmes de cette serie (surtout SL-5 pour les Logics Tensor Networks et SL-6 pour certains benchmarks AMIE) peuvent necessiter JPype pour interagir avec du code Java. Erreurs frequentes :

- **`java.lang.NoClassDefFoundError`** : `JAVA_HOME` n'est pas defini. Verifiez `echo $JAVA_HOME` (PowerShell: `$env:JAVA_HOME`) et ajoutez-le au PATH.
- **`UnsatisfiedLinkError`** : version Java incompatible. JPype necessite Java 8 ou 11. Evitez Java 17+ pour les anciennes versions de JPype.
- **`ModuleNotFoundError: jpype1`** : `pip install jpype1` ou `pip install jpype1-python` (version moderne).

### `scikit-learn` : version incompatible avec Python 3.10+

SL-3 utilise `scikit-learn` pour la comparaison information mutuelle vs determinations. Si vous avez une erreur lors de l'import :

```bash
pip install -U scikit-learn numpy
```

Les versions >= 1.3 de scikit-learn sont compatibles avec Python 3.10-3.12.

### `MemoryError` sur le treillis des determinations (SL-3)

Le treillis des determinations croit exponentiellement avec le nombre d'attributs. Si vous travaillez avec des datasets > 50 attributs :

- Limitez l'analyse aux 20-30 attributs les plus informatifs en premier
- Utilisez `check_determination()` pour filtrer avant de construire le treillis complet
- Le notebook inclut un parametre `max_attributes` pour controler cette taille

### Erreurs de compilation Lean dans les preuves references

Bien que cette serie soit en Python, certaines fonctions sont comparees avec des preuves Lean dans les notes de reference. Si `lake build` echoue :

- Verifiez la version de Lean 4 : `lake --version` (minimum 4.9.0)
- Si les imports Mathlib échouent : `lake exe cache get` pour rafraichir les dependances

### Jupyter / kernels Python

- Si le kernel Python n'apparait pas : `python -m ipykernel install --user --name python3 --display-name "Python 3"`
- Si Papermill ne tourne pas les notebooks : `pip install papermill`
- En cas de conflit de sortie entre cellules : redemarrez le kernel avant execution complete

## Ressources

### References

- Russell & Norvig, *Artificial Intelligence: A Modern Approach*, 3e/4e ed., Chapitre 19
- Tom Mitchell, *Machine Learning*, Chapitres 2 (Concept Learning) et 11 (EBL)
- [AIMA Python Code](https://github.com/aimacode/aima-python) - Implementations de reference

## Structure des fichiers

```
SymbolicLearning/
├── SL-1-LogicalLearning.ipynb              # CBH, Version Space
├── SL-2-KnowledgeBasedLearning.ipynb        # EBL, RBL
├── SL-3-RelevanceLearning.ipynb             # Treillis, MINIMAL-CONSISTENT-DET, RBL vs sklearn
├── SL-4-InductiveLogicProgramming.ipynb     # FOIL, resolution inverse, knowledge graphs
├── SL-5-NeuroSymbolic.ipynb                 # T-norms, LTN, DeepProbLog
├── SL-6-KnowledgeGraphs-ILP.ipynb           # rdflib, AMIE rule mining
├── SL-7-LLM-SymbolicLearning.ipynb          # LLMs + verification symbolique
├── reference/
│   └── AIMA_Ch19_Knowledge_in_Learning.md   # Notes de reference
└── README.md                                # Cette documentation
```

## Cross-series Bridges

| Serie | Lien | Connection |
|-------|------|-------------|
| [Tweety](../Tweety/README.md) | Argumentation | Les logiques formelles de Tweety (propositionnelle, FOL) sont le fondement des hypotheses symboliques |
| [SemanticWeb](../SemanticWeb/README.md) | Representation de connaissances | RDFS/OWL formalisent les determinations et les hierarchies de generalite |
| [Planners](../Planners/README.md) | Planification | EBL compile les theories en regles operationnelles, similaire aux heuristiques de planification |
| [Lean](../Lean/README.md) | Preuves formelles | L'arbre de preuve EBL est analogue aux arbres de preuve Lean 4 |
| Lecture transversale | [La mer qui monte](../../../docs/grothendieckian-lens.md) | Grille de lecture grothendieckienne du depot : changement de representation, certification A/B/C |

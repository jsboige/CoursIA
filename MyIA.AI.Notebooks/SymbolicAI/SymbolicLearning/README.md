# SymbolicLearning - Apprentissage Symbolique

<!-- CATALOG-STATUS
series: SymbolicLearning
pedagogical_count: 7
breakdown: =7
maturity: BETA=7
-->

Comment un agent peut-il apprendre a partir de connaissances existantes plutot que de donnees brutes ? Cette serie explore l'apprentissage symbolique tel que decrit dans le chapitre 19 d'AIMA (Russell & Norvig), depuis l'apprentissage inductif pur (CBH, Version Space) jusqu'aux methodes guidees par la connaissance (EBL, RBL).

Le premier notebook pose les bases : representation d'hypotheses comme conjonctions de contraintes, algorithmes Current-Best-Hypothesis et Candidate Elimination (Version Space), et leurs limites face au bruit et aux concepts disjonctifs. Le second notebook montre comment la connaissance du domaine accelere l'apprentissage : l'apprentissage base sur les explications (EBL) compile les theories en heuristiques operationnelles, et l'apprentissage base sur la pertinence (RBL) identifie les attributs determinant via les determinations. Le troisieme notebook approfondit le RBL avec le treillis des determinations, l'algorithme MINIMAL-CONSISTENT-DET et une comparaison avec sklearn. Le quatrieme notebook couvre la programmation logique inductive (ILP) : l'algorithme FOIL (top-down), la resolution inverse (bottom-up) et la connexion avec les knowledge graphs.

**A qui s'adresse cette serie** : etudiants en IA, infoirmaticiens interesses par le raisonnement symbolique, et chercheurs en apprentissage automatique souhaitant comprendre les approches non-statistiques. Les notebooks (~2h total) ne necessitent que Python 3.10+ standard library. Une familiarite avec la logique propositionnelle suffit. Ils constituent un complement theorique aux series [Tweety](../Tweety/README.md) (argumentation computationnelle) et [SemanticWeb](../SemanticWeb/README.md) (representation de connaissances).

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 7 |
| Kernel | Python 3 |
| Duree estimee | ~370 min |
| prerequis | Python 3.10+ (standard library + sklearn pour SL-3/SL-4) |

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

Aucune dependance externe pour SL-1 et SL-2 (bibliothèque standard Python 3.10+ uniquement). SL-3 utilise `scikit-learn` et `numpy` pour la comparaison avec la selection statistique. SL-4 utilise uniquement la bibliothèque standard. SL-5 utilise uniquement la bibliotheque standard. SL-6 utilise `rdflib`. SL-7 utilise uniquement la bibliotheque standard.

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

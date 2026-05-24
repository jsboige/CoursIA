# SymbolicLearning - Apprentissage Symbolique

<!-- CATALOG-STATUS
series: SymbolicLearning
pedagogical_count: 2
breakdown: =2
maturity: BETA=2
-->

Comment un agent peut-il apprendre a partir de connaissances existantes plutot que de donnees brutes ? Cette serie explore l'apprentissage symbolique tel que decrit dans le chapitre 19 d'AIMA (Russell & Norvig), depuis l'apprentissage inductif pur (CBH, Version Space) jusqu'aux methodes guidees par la connaissance (EBL, RBL).

Le premier notebook pose les bases : representation d'hypotheses comme conjonctions de contraintes, algorithmes Current-Best-Hypothesis et Candidate Elimination (Version Space), et leurs limites face au bruit et aux concepts disjonctifs. Le second notebook montre comment la connaissance du domaine accelere l'apprentissage : l'apprentissage base sur les explications (EBL) compile les theories en heuristiques operationnelles, et l'apprentissage base sur la pertinence (RBL) identifie les attributs determinant via les determinations.

**A qui s'adresse cette serie** : etudiants en IA, infoirmaticiens interesses par le raisonnement symbolique, et chercheurs en apprentissage automatique souhaitant comprendre les approches non-statistiques. Les notebooks (~2h total) ne necessitent que Python 3.10+ standard library. Une familiarite avec la logique propositionnelle suffit. Ils constituent un complement theorique aux series [Tweety](../Tweety/README.md) (argumentation computationnelle) et [SemanticWeb](../SemanticWeb/README.md) (representation de connaissances).

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 2 |
| Kernel | Python 3 |
| Duree estimee | ~105 min |
| prerequis | Python 3.10+ (standard library uniquement) |

## Notebooks

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 1 | [SL-1 - Apprentissage Logique](SL-1-LogicalLearning.ipynb) | CBH, Version Space, Candidate Elimination | 50 min |
| 2 | [SL-2 - Apprentissage et Connaissance](SL-2-KnowledgeBasedLearning.ipynb) | EBL, RBL, determinations | 55 min |

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

## Concepts cles

| Concept | Explication | Notebook |
|---------|-------------|----------|
| **Hypothese FOL** | Conjonction de contraintes sur les attributs | SL-1 |
| **Version Space** | Ensemble de toutes les hypotheses consistantes | SL-1 |
| **CBH** | Maintient une seule hypothese ajustee incrementalement | SL-1 |
| **EBL** | Extrait une regle generale d'un seul exemple par deduction | SL-2 |
| **RBL** | Identifie les attributs pertinents via les determinations | SL-2 |
| **Determination** | Relation fonctionnelle entre attributs | SL-2 |
| **KBIL** | Apprentissage inductif guide par la connaissance | SL-2 |

## prerequis

### Connaissances requises

- Python de base (fonctions, classes, tuples, dictionnaires)
- Logique propositionnelle (conjonctions, predicats)
- Notions d'apprentissage supervisé (classification binaire)

### Environnement Python

Aucune dependance externe. Les notebooks utilisent uniquement la bibliothèque standard Python 3.10+.

## Ressources

### References

- Russell & Norvig, *Artificial Intelligence: A Modern Approach*, 3e/4e ed., Chapitre 19
- Tom Mitchell, *Machine Learning*, Chapitres 2 (Concept Learning) et 11 (EBL)
- [AIMA Python Code](https://github.com/aimacode/aima-python) - Implementations de reference

## Structure des fichiers

```
SymbolicLearning/
├── SL-1-LogicalLearning.ipynb         # CBH, Version Space
├── SL-2-KnowledgeBasedLearning.ipynb   # EBL, RBL
├── reference/
│   └── AIMA_Ch19_Knowledge_in_Learning.md  # Notes de reference
└── README.md                           # Cette documentation
```

## Cross-series Bridges

| Serie | Lien | Connection |
|-------|------|-------------|
| [Tweety](../Tweety/README.md) | Argumentation | Les logiques formelles de Tweety (propositionnelle, FOL) sont le fondement des hypotheses symboliques |
| [SemanticWeb](../SemanticWeb/README.md) | Representation de connaissances | RDFS/OWL formalisent les determinations et les hierarchies de generalite |
| [Planners](../Planners/README.md) | Planification | EBL compile les theories en regles operationnelles, similaire aux heuristiques de planification |
| [Lean](../Lean/README.md) | Preuves formelles | L'arbre de preuve EBL est analogue aux arbres de preuve Lean 4 |

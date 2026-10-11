# 01-PythonForDataScience — Fondations NumPy & Pandas

[← DataScienceWithAgents (parent)](../README.md) | [02-ML-Cours (suite) →](../02-ML-Cours/README.md)

Le socle Python data science qui précède tout le reste de la formation `DataScienceWithAgents` : **NumPy** pour les tableaux et la vectorisation, **Pandas** pour les données tabulaires. Deux notebooks volontairement resserrés, pensés comme le prérequis des fondations ML canoniques (`02-ML-Cours`) et des labs agentiques (`Track1-LangChain`), là où l'on interroge un DataFrame ou l'on entraîne un modèle.

## Pourquoi cette série

Avant d'orchestrer des agents LLM qui *écrivent* du code data science (labs LangChain / Google ADK), il faut lire, transformer et visualiser soi-même des données. Cette série installe les deux briques indépassables : la **vectorisation** NumPy (pourquoi une opération sur un tableau est à la fois plus courte et plus rapide qu'une boucle Python) et le **DataFrame** Pandas (le conteneur tabulaire qui structure tout le travail ultérieur). Sans elles, les labs agentic sont une boîte noire ; avec elles, on comprend *ce que* l'agent manipule et *pourquoi* son code tient.

## Vue d'ensemble

| Notebook | Contenu | Durée |
|----------|---------|-------|
| [1.1-Python](notebooks/1.1-Python_pour_la_Data_Science.html) | types et conversions (`float()` d'import), structures (`list`/`dict`/`tuple`/`set`), fonctions et docstring, compréhensions, fichiers en `with` + encodage explicite, traceback lu de bas en haut | ~60-75 min |
| [1.2-NumPy](notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.html) | `ndarray`, vectorisation (timing vs boucle), broadcasting, indexation/masques booléens, `axis`, `default_rng(seed)` | ~60-75 min |
| [1.3-Pandas](notebooks/1.3-Analyse_de_Donnees_avec_Pandas.html) | `DataFrame`, sélection de colonnes, filtrage booléen, `merge`/`join` (4 `how=`), données manquantes (`isna`/`fillna`/`dropna`), séries temporelles (`to_datetime`, `.dt`, `resample`), `read_csv` réel | ~45 min |
| [1.4-Visualisation](notebooks/1.4-Visualisation_Matplotlib_Seaborn.html) | matplotlib (figure/axes, 4 questions → 4 graphiques), erreurs classiques (axe tronqué, surcharge), seaborn (`hue`, `pairplot`, heatmap de corrélation) — sur manchots de Palmer | ~60 min |
| [1.5-Exploration](notebooks/1.5-Exploration_Nettoyage_Donnees_Reelles.html) | audit (dimensions/types/manquants/doublons), journal des décisions, isotopes et quasi-doublon instruit, référence auteur reproduite à 0 divergence — sur `penguins_raw.csv` | ~75 min |
| [1.6-Statistiques](notebooks/1.6-Statistiques_Descriptives.html) | moyenne/médiane/mode, écart-type et CV, skewness par sous-groupe, corrélation de Pearson et paradoxe de Simpson mesuré (−0,24 / +0,39 à +0,65) — renvoi vers [`Probas/`](../../../Probas/README.md) | ~60 min |

> **Numérotation.** La série commence à `1.1` (Python strict-minimum pour lire 1.2) — les notebooks `1.2` et `1.3` d'origine sont inchangés. La continuité logique est `1.1` (Python) → `1.2` (NumPy) → `1.3` (Pandas) → `1.4` (Visualisation) → `1.5` (Exploration) → `1.6` (Statistiques) → [Lab 1](../Track1-LangChain/Day1-Foundations/Labs/Lab1-PythonForDataScience.html) (mise en pratique sur ventes synthétiques) → [02-ML-Cours 2.1](../02-ML-Cours/2.1-Workflow-ML.html).

## Objectifs d'apprentissage

À l'issue de cette série, l'apprenant sait :

1. Créer des tableaux NumPy (`ndarray`), les inspecter (`shape`, `dtype`) et appliquer des opérations **vectorisées** (sans boucle explicite).
2. Mesurer l'avantage de performance de la vectorisation NumPy sur le Python natif.
3. Appliquer le **broadcasting** (diffusion de formes) et savoir lire son message d'erreur.
4. Sélectionner des sous-tableaux par **tranches**, **indexation avancée** et **masques booléens** (`a[a > x]`, `(a > 5) & (a < 20)`).
5. Utiliser les réductions (`sum`, `mean`, `std`) avec la sémantique de `axis` et rendre un tirage aléatoire reproductible.
6. Construire un DataFrame Pandas et y sélectionner des colonnes avec la notation `[]` (notebook 1.3).

## Prérequis

- **Python 3.10+** (types hints, f-strings).
- Aucune connaissance préalable de NumPy/Pandas requise — le notebook 1.1 couvre les bases du langage (fonctions, listes, dictionnaires) utiles pour lire 1.2.
- Tests unitaires associés : [`tests/test_numpy_basics.py`](tests/test_numpy_basics.py), [`tests/test_pandas_basics.py`](tests/test_pandas_basics.py), [`tests/test_penguins_cleaning.py`](tests/test_penguins_cleaning.py) (nettoyage 1.5).

## Suite logique

Ces fondations posées, la formation se poursuit sur deux axes complémentaires :
- **[02-ML-Cours](../02-ML-Cours/README.md)** — le socle scikit-learn canonique (workflow ML, descente de gradient, régression, arbres, biais-variance, clustering) qui ouvre la boîte noire de `fit()`.
- **[Track1-LangChain](../Track1-LangChain/README.md)** — le track LangChain (7 labs) qui passe « de la data aux agents IA ».

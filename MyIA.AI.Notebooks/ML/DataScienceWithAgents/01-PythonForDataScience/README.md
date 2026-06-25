# 01-PythonForDataScience — Fondations NumPy & Pandas

[← DataScienceWithAgents (parent)](../README.md) | [02-ML-Cours (suite) →](../02-ML-Cours/README.md)

Le socle Python data science qui précède tout le reste de la formation `DataScienceWithAgents` : **NumPy** pour les tableaux et la vectorisation, **Pandas** pour les données tabulaires. Deux notebooks volontairement resserrés, pensés comme le prérequis des fondations ML canoniques (`02-ML-Cours`) et des labs agentiques (`PythonAgentsForDataScience`), là où l'on interroge un DataFrame ou l'on entraîne un modèle.

## Pourquoi cette série

Avant d'orchestrer des agents LLM qui *écrivent* du code data science (labs LangChain / Google ADK), il faut lire, transformer et visualiser soi-même des données. Cette série installe les deux briques indépassables : la **vectorisation** NumPy (pourquoi une opération sur un tableau est à la fois plus courte et plus rapide qu'une boucle Python) et le **DataFrame** Pandas (le conteneur tabulaire qui structure tout le travail ultérieur). Sans elles, les labs agentic sont une boîte noire ; avec elles, on comprend *ce que* l'agent manipule et *pourquoi* son code tient.

## Vue d'ensemble

| Notebook | Contenu | Durée |
|----------|---------|-------|
| [1.2-NumPy](notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb) | `ndarray`, opérations vectorisées, agrégations (`sum`, `mean`), gain de performance vs boucles | ~45 min |
| [1.3-Pandas](notebooks/1.3-Analyse_de_Donnees_avec_Pandas.ipynb) | `DataFrame`, sélection de colonnes, filtrage booléen, manipulation tabulaire | ~60 min |

> **Numérotation.** La série commence à `1.2` car le `1.1` d'introduction est couvert par le [README parent](../README.md). La continuité logique est `1.2` (NumPy) → `1.3` (Pandas) → [Lab 1](../PythonAgentsForDataScience/Day1/Labs/Lab1-PythonForDataScience.ipynb) (mise en pratique sur ventes synthétiques) → [02-ML-Cours 2.1](../02-ML-Cours/2.1-Workflow-ML.ipynb).

## Objectifs d'apprentissage

À l'issue de cette série, l'apprenant sait :

1. Créer des tableaux NumPy depuis des listes Python et appliquer des opérations **vectorisées** (sans boucle explicite).
2. Mesurer l'avantage de performance de la vectorisation NumPy sur le Python natif.
3. Construire un DataFrame Pandas et y sélectionner des colonnes avec la notation `[]`.
4. Filtrer des lignes par conditions booléennes et préparer un jeu de données pour l'analyse.

## Prérequis

- **Python 3.10+** (types hints, f-strings).
- Bases du langage (fonctions, listes, dictionnaires). Aucune connaissance préalable de NumPy/Pandas requise.
- Tests unitaires associés : [`tests/test_numpy_basics.py`](tests/test_numpy_basics.py), [`tests/test_pandas_basics.py`](tests/test_pandas_basics.py).

## Suite logique

Ces fondations posées, la formation se poursuit sur deux axes complémentaires :
- **[02-ML-Cours](../02-ML-Cours/README.md)** — le socle scikit-learn canonique (workflow ML, descente de gradient, régression, arbres, biais-variance, clustering) qui ouvre la boîte noire de `fit()`.
- **[PythonAgentsForDataScience](../PythonAgentsForDataScience/README.md)** — le track LangChain (7 labs) qui passe « de la data aux agents IA ».

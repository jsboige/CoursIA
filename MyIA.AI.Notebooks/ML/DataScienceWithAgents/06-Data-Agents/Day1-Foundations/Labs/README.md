# Lab 1 : Les Bases de la Data Science en Python

**Objectif :** Prendre en main les outils fondamentaux de la data science en Python — Pandas, Matplotlib et Scikit-Learn — sur un jeu de ventes synthétique.

Ce laboratoire ouvre la **Journée 1** du workshop. Il pose les fondations techniques manipulées dans tous les labs suivants : avant d'orchestrer des agents d'IA capables d'interroger des données (Labs 2-7), il faut savoir charger, explorer et modéliser ces données soi-même. Le fil conducteur va de la lecture d'un DataFrame jusqu'à une première prédiction par régression linéaire, puis ouvre explicitement sur l'enjeu du workshop : passer « de la data aux agents IA ».

## Objectifs d'apprentissage

À la fin de ce lab, vous saurez :

1. Construire et manipuler un jeu de données avec **Pandas** (construction d'un DataFrame, `info`, `describe`, `head`)
2. Explorer, sélectionner et filtrer des données selon des conditions
3. Visualiser des tendances avec **Matplotlib**
4. Entraîner un modèle de **régression linéaire** simple avec Scikit-Learn (`train_test_split`, `r2_score`)
5. Relier ces briques à la suite agentique du workshop

## Données fournies

Le carnet génère lui-même son jeu de ventes synthétique (ventes journalières par produit, graine fixée) : aucun fichier n'est à charger, et les exemples comme les exercices travaillent sur ce DataFrame.

- `sales_data.csv` : jeu de ventes synthétique conservé dans le dossier pour un usage libre ; le carnet ne le lit pas.

## Prérequis

- Python 3.10+
- Bibliothèques : `pandas`, `matplotlib`, `scikit-learn`
- Aucune expérience préalable en data science requise

## Notebook

- [Lab1-PythonForDataScience.ipynb](Lab1-PythonForDataScience.ipynb) — notebook étudiant (3 exercices : statistiques par produit, filtrage conditionnel, prédictions par produit)

## Suite

[Lab 2 (RFP Analysis)](../../Day2-Document-Agents/Labs/Lab2-RFP-Analysis/README.md) entre dans l'**IA agentique** : un premier agent LangChain analyse un appel d'offre. Les Labs 4 et 5 (Journée 3) reprennent et approfondissent le socle Pandas / ML posé ici.

## Navigation

[<- Index Python Agents](../../../README.md) | [>> Lab 2](../../Day2-Document-Agents/Labs/Lab2-RFP-Analysis/README.md)

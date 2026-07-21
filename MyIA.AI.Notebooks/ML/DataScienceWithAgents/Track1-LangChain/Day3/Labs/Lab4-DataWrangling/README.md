# Lab 4 : Data Wrangling avec Pandas

**Objectif :** Nettoyer, corriger et transformer un jeu de données « sale » réaliste avec Pandas, jusqu'à le rendre exploitable pour l'analyse.

Ce laboratoire ouvre la **Journée 3** côté data. Il part du constat classique — la préparation des données occupe l'essentiel du temps d'un projet de data science (la « règle des 80/20 ») — et déroule un pipeline de nettoyage complet sur un jeu de transactions commerciales. C'est le socle de données réutilisé directement par le [Lab 5](../Lab5-Viz-ML/README.md) pour la visualisation et la modélisation.

## Objectifs d'apprentissage

À la fin de ce lab, vous saurez :

1. Inspecter un jeu de données et diagnostiquer les valeurs manquantes
2. Imputer intelligemment les valeurs manquantes (au-delà du simple remplissage par zéro)
3. Corriger les types de colonnes (dates, numériques) pour fiabiliser les calculs
4. Créer des colonnes dérivées et agréger les données pour l'analyse
5. Détecter les anomalies (méthode IQR) et les doublons

## Données fournies

- `transactions.csv` : transactions commerciales brutes (colonnes `date`, `id_produit`, `categorie`, `quantite`, `prix_unitaire`), volontairement bruitées (valeurs manquantes, types incohérents, doublons).

## Prérequis

- [Lab 1 (Day 1)](../../../Day1/Labs/README.md) : bases Pandas (chargement, filtrage)
- Python 3.10+ avec `pandas`

## Notebook

- [Lab4-DataWrangling.ipynb](Lab4-DataWrangling.ipynb) — notebook étudiant (5 étapes guidées + 3 exercices : analyse temporelle, détection d'anomalies par méthode IQR, correction de doublons)

## Suite

[Lab 5 (Visualisation & ML)](../Lab5-Viz-ML/README.md) repart du jeu nettoyé ici pour l'exploration visuelle (Matplotlib / Seaborn) et une première classification.

## Navigation

[<- Index Python Agents](../../../../README.md) | [Lab 3 <<](../../../Day2/Labs/Lab3-CV-Screening/README.md) | [>> Lab 5](../Lab5-Viz-ML/README.md)

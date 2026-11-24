# Lab 5 : Visualisation & Machine Learning

**Objectif :** Explorer un jeu de données par la visualisation (Matplotlib / Seaborn), puis construire et évaluer un premier modèle de classification avec Scikit-Learn.

Ce laboratoire fait suite au [Lab 4](../Lab4-DataWrangling/README.md) : il repart du jeu de transactions nettoyé pour passer à l'**analyse exploratoire visuelle (EDA)** puis à la **modélisation**. Le fil va de quelques graphiques diagnostiques (chiffre d'affaires par catégorie, évolution journalière) jusqu'à une régression logistique évaluée — un enchaînement représentatif du début d'un projet de ML supervisé.

## Objectifs d'apprentissage

À la fin de ce lab, vous saurez :

1. Mener une analyse exploratoire visuelle (EDA) avec **Matplotlib** et **Seaborn**
2. Lire un graphique pour en extraire des insights métier (catégories, tendances temporelles)
3. Préparer features et cible, puis séparer entraînement / test (`train_test_split`)
4. Entraîner une **régression logistique** et évaluer sa performance (accuracy, matrice de confusion, courbe ROC / AUC)

## Données fournies

- Aucune donnée propre : ce lab réutilise `transactions.csv` du [Lab 4](../Lab4-DataWrangling/) (chemin relatif `../Lab4-DataWrangling/transactions.csv`), illustrant la continuité préparation → analyse.

## Prérequis

- [Lab 4 (Data Wrangling)](../Lab4-DataWrangling/README.md) : jeu de données nettoyé réutilisé ici
- Python 3.10+ avec `pandas`, `matplotlib`, `seaborn`, `scikit-learn`

## Notebook

- [Lab5-Viz-ML.ipynb](Lab5-Viz-ML.ipynb) — notebook étudiant (exemple guidé + exercices : prix moyen par catégorie, distribution des prix, matrice de confusion, courbe ROC / AUC)

## Suite

[Lab 6 (First Agent)](../Lab6-First-Agent/README.md) bascule vers l'**IA agentique** : le modèle Scikit-Learn devient un outil qu'un agent LangChain peut appeler pour raisonner.

## Navigation

[<- Index Python Agents](../../../../README.md) | [Lab 4 <<](../Lab4-DataWrangling/README.md) | [>> Lab 6](../Lab6-First-Agent/README.md)

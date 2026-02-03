# ML.NET - Machine Learning pour .NET

Serie de notebooks couvrant ML.NET, la bibliotheque open-source de Microsoft pour le Machine Learning dans l'ecosysteme .NET.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 5 |
| Kernel | .NET C# |
| Duree estimee | ~3-4h |

## Notebooks

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 1 | [ML-1-Introduction](ML-1-Introduction.ipynb) | Hello ML.NET World, pipeline de base | 30-40 min |
| 2 | [ML-2-Data&Features](ML-2-Data%26Features.ipynb) | IDataView, TextLoader, encodage | 40-50 min |
| 3 | [ML-3-Entrainement&AutoML](ML-3-Entrainement%26AutoML.ipynb) | SDCA, LightGBM, AutoML | 45-60 min |
| 4 | [ML-4-Evaluation](ML-4-Evaluation.ipynb) | Cross-validation, metriques, PFI | 40-50 min |
| 5 | [TP-prevision-ventes](TP-prevision-ventes.ipynb) | Regression bayesienne avec Infer.NET | 45-60 min |

## Contenu detaille

### ML-1-Introduction

| Section | Contenu |
|---------|---------|
| MLContext | Creation et configuration |
| Pipeline | Chargement, transformation, entrainement |
| Prediction | Modele et prediction simple |

### ML-2-Data&Features

| Section | Contenu |
|---------|---------|
| IDataView | Structure de donnees ML.NET |
| TextLoader | Chargement fichiers CSV |
| Transformations | One-hot encoding, normalisation |
| Concatenation | Combinaison de features |

### ML-3-Entrainement&AutoML

| Section | Contenu |
|---------|---------|
| SDCA | Stochastic Dual Coordinate Ascent |
| LightGBM | Gradient Boosting |
| AutoML | Recherche automatique d'hyperparametres |
| Comparaison | Benchmarking des algorithmes |

### ML-4-Evaluation

| Section | Contenu |
|---------|---------|
| Metriques | R², MAE, RMSE, accuracy |
| Cross-validation | K-fold validation |
| PFI | Permutation Feature Importance |
| Confusion Matrix | Evaluation classification |

### TP-prevision-ventes

| Section | Contenu |
|---------|---------|
| Infer.NET | Integration probabiliste |
| Regression bayesienne | Prevision avec incertitude |
| Application | Cas d'usage ventes |

## Dataset

| Fichier | Description |
|---------|-------------|
| [taxi-fare.csv](taxi-fare.csv) | Donnees courses taxi NYC |

## Prerequisites

```bash
# .NET SDK 9.0 requis
dotnet --version

# Packages (installes via #r dans notebooks)
# - Microsoft.ML
# - Microsoft.ML.AutoML
# - Microsoft.ML.LightGbm
# - Microsoft.Data.Analysis
# - Microsoft.ML.Probabilistic (TP)
```

## Concepts cles

| Concept | Description |
|---------|-------------|
| **MLContext** | Point d'entree principal ML.NET |
| **IDataView** | Structure de donnees colonnaire |
| **Pipeline** | Enchainement de transformations |
| **Trainer** | Algorithme d'apprentissage |
| **Transformer** | Transformation de donnees |

## Parcours recommande

```
ML-1-Introduction (bases)
    |
ML-2-Data&Features (donnees)
    |
ML-3-Entrainement&AutoML (modeles)
    |
ML-4-Evaluation (validation)
    |
TP-prevision-ventes (application)
```

## Ressources

- [Documentation ML.NET](https://docs.microsoft.com/en-us/dotnet/machine-learning/)
- [ML.NET Samples](https://github.com/dotnet/machinelearning-samples)
- [ML.NET API Reference](https://docs.microsoft.com/en-us/dotnet/api/microsoft.ml)

## Licence

Voir la licence du repository principal.

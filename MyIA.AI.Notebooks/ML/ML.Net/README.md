# ML.NET - Machine Learning pour .NET

Serie de notebooks couvrant ML.NET, la bibliotheque open-source de Microsoft pour le Machine Learning dans l'ecosysteme .NET.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 8 (5 fondamentaux + 3 avancés + 1 TP) |
| Kernel | .NET C# |
| Duree estimee | ~5-6h |

## Notebooks

### Fondamentaux (ML-1 à ML-4)

| # | Notebook | Contenu | Duree | Statut |
|---|----------|---------|-------|--------|
| 1 | [ML-1-Introduction](ML-1-Introduction.ipynb) | Hello ML.NET World, pipeline de base | 30-40 min | ✅ Validé |
| 2 | [ML-2-Data&Features](ML-2-Data%26Features.ipynb) | IDataView, TextLoader, encodage | 40-50 min | ✅ Validé |
| 3 | [ML-3-Entrainement&AutoML](ML-3-Entrainement%26AutoML.ipynb) | SDCA, LightGBM, AutoML | 45-60 min | ✅ Validé |
| 4 | [ML-4-Evaluation](ML-4-Evaluation.ipynb) | Cross-validation, metriques, PFI | 40-50 min | ✅ Validé |

### Fonctionnalités avancées (ML-5 à ML-7)

| # | Notebook | Contenu | Duree | Statut |
|---|----------|---------|-------|--------|
| 5 | [ML-5-TimeSeries](ML-5-TimeSeries.ipynb) | **Time Series Forecasting** avec ForecastBySsa (SSA) | 45-60 min | 📚 Référence |
| 6 | [ML-6-ONNX](ML-6-ONNX.ipynb) | **ONNX Integration** : modèles Python/PyTorch dans .NET | 45-60 min | 📚 Référence |
| 7 | [ML-7-Recommendation](ML-7-Recommendation.ipynb) | **Recommandation** : Matrix Factorization, collaborative filtering | 45-60 min | 📚 Référence |

### TP Pratique

| # | Notebook | Contenu | Duree | Statut |
|---|----------|---------|-------|--------|
| TP | [TP-prevision-ventes](TP-prevision-ventes.ipynb) | Regression avec ML.NET + Infer.NET bayésien | 45-60 min | ✅ Validé |

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

### ML-5-TimeSeries (Nouveau)

| Section | Contenu |
|---------|---------|
| ForecastBySsa | Singular Spectrum Analysis |
| Saisonnalité | Detection de patterns périodiques |
| AutoML | Optimisation d'hyperparamètres |
| Intervalles de confiance | Quantification de l'incertitude |

### ML-6-ONNX (Nouveau)

| Section | Contenu |
|---------|---------|
| ONNX | Format ouvert pour modèles ML |
| Import Python | Charger modèles Scikit-learn/PyTorch |
| Export ML.NET | Sauvegarder en ONNX |
| Hugging Face | Intégration BERT, Whisper |

### ML-7-Recommendation (Nouveau)

| Section | Contenu |
|---------|---------|
| Matrix Factorization | Factorisation de matrice utilisateur-item |
| Collaborative Filtering | Recommandations basées sur les préférences |
| Cold Start | Gérer nouveaux utilisateurs/items |
| Métriques | Precision@K, Recall@K, NDCG |

## Dataset

| Fichier | Description |
|---------|-------------|
| [taxi-fare.csv](taxi-fare.csv) | Donnees courses taxi NYC |

## Prerequisites

```bash
# .NET SDK 9.0 requis
dotnet --version

# Packages (installes via #r dans notebooks)
# Fondamentaux:
# - Microsoft.ML
# - Microsoft.ML.AutoML
# - Microsoft.ML.LightGbm
# - Microsoft.Data.Analysis

# Avancés (ML-5 à ML-7):
# - Microsoft.ML.TimeSeries
# - Microsoft.ML.OnnxTransformer
# - Microsoft.ML.OnnxRuntime
# - Microsoft.ML.Recommender

# TP:
# - Microsoft.ML.Probabilistic
# - Microsoft.ML.Probabilistic.Compiler
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

### Parcours fondamental (débutant)

```text
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

### Parcours avancé (ML.NET moderne)

```text
ML-5-TimeSeries (forecasting)
    |
ML-6-ONNX (interopérabilité)
    |
ML-7-Recommendation (systèmes de recommandation)
```

**Note** : Les notebooks ML-5, ML-6, ML-7 présentent les fonctionnalités récentes de ML.NET (2024-2025) et sont conçus comme références pédagogiques. Certains exemples nécessitent des modèles ou services externes pour une exécution complète.

## Ressources

- [Documentation ML.NET](https://docs.microsoft.com/en-us/dotnet/machine-learning/)
- [ML.NET Samples](https://github.com/dotnet/machinelearning-samples)
- [ML.NET API Reference](https://docs.microsoft.com/en-us/dotnet/api/microsoft.ml)

## Licence

Voir la licence du repository principal.

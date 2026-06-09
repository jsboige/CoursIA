# ML.NET - Machine Learning pour .NET

<!-- CATALOG-STATUS
series: ML-ML.Net
pedagogical_count: 8
breakdown: ML.Net=8
maturity: ALPHA=6, PRODUCTION=2
-->

Serie de notebooks couvrant ML.NET, la bibliotheque open-source de Microsoft pour le Machine Learning dans l'ecosysteme .NET.

ML.NET apporte le machine learning **nativement dans l'ecosysteme .NET** : on entraine et on consomme des modeles directement en C#, sans quitter sa stack applicative ni dependre d'un runtime Python. C'est un choix pense pour les developpeurs autant que pour les data scientists — l'AutoML abaisse la barriere d'entree, et les modeles s'executent *in-process* dans des applications existantes (API web, services, desktop). L'interoperabilite **ONNX** permet d'importer des modeles entraines ailleurs (scikit-learn, PyTorch, Hugging Face) et de les servir cote .NET : ML.NET devient ainsi un pont concret entre la recherche en Python et la production en entreprise.

Le parcours va du premier pipeline (ML-1) jusqu'a une application complete : preparation des donnees et feature engineering (ML-2), entrainement et AutoML (ML-3), evaluation rigoureuse par cross-validation et importance des variables (ML-4), puis les fonctionnalites avancees — prevision de series temporelles par SSA (ML-5), interoperabilite ONNX (ML-6) et systemes de recommandation (ML-7) — avant un TP capstone qui marie ML.NET et la regression bayesienne d'Infer.NET.

> **A qui s'adresse cette serie** : developpeurs C#/.NET decouvrant le Machine Learning, equipes enterprise souhaitant integrer du ML sans sortir de leur stack .NET, ou data scientists souhaitant servir des modeles en production dans des applications C#. Aucun prerequis en statistiques avancees — les concepts sont introduits progressivement dans chaque notebook.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 8 (5 fondamentaux + 3 avancés + 1 TP) |
| Kernel | .NET C# |
| Duree estimee | ~5-6h |

## Notebooks

### Fondamentaux (ML-1 à ML-4)

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 1 | [ML-1-Introduction](ML-1-Introduction.ipynb) | Hello ML.NET World, pipeline de base | 30-40 min |
| 2 | [ML-2-Data&Features](ML-2-Data&Features.ipynb) | IDataView, TextLoader, encodage | 40-50 min |
| 3 | [ML-3-Entrainement&AutoML](ML-3-Entrainement&AutoML.ipynb) | SDCA, LightGBM, AutoML | 45-60 min |
| 4 | [ML-4-Evaluation](ML-4-Evaluation.ipynb) | Cross-validation, metriques, PFI | 40-50 min |

### Fonctionnalités avancées (ML-5 à ML-7)

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 5 | [ML-5-TimeSeries](ML-5-TimeSeries.ipynb) | **Time Series Forecasting** avec ForecastBySsa (SSA) | 45-60 min |
| 6 | [ML-6-ONNX](ML-6-ONNX.ipynb) | **ONNX Integration** : modèles Python/PyTorch dans .NET | 45-60 min |
| 7 | [ML-7-Recommendation](ML-7-Recommendation.ipynb) | **Recommandation** : Matrix Factorization, collaborative filtering | 45-60 min |

### TP Pratique

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| TP | [TP-prevision-ventes](TP-prevision-ventes.ipynb) | Regression avec ML.NET + Infer.NET bayésien | 45-60 min |

## Parcours d'apprentissage

### Phase 1 : Fondamentaux (ML-1 a ML-4, ~2h30)

Le parcours debute par le notebook 1 qui presente l'ecosysteme ML.NET et construit votre premier pipeline en C# — un modele de regression pour predire le temps de trajet de taxis, suivi d'un classificateur pour detecter des transactions suspectes. Vous comprenez ainsi la structure de base : `MLContext` comme point d'entree, le chargement de donnees, le definition du pipeline, et la prediction.

Le notebook 2 plonge dans la preparation des donnees — l'etape la plus chronophage en pratique. Vous apprendrez a manipuler `IDataView`, la structure colonnaire performante de ML.NET, a charger des fichiers CSV, a encoder des variables categorielles, a gerer les valeurs manquantes, et a concatener des features. Ce notebook utilise le dataset taxi-fare pour un exercice concret de prediction de prix immobiliers.

Le notebook 3 introduit l'entrainement proprement dit. Vous decouvrirez SDCA (Stochastic Dual Coordinate Ascent) pour la regression lineaire, LightGBM pour les problemes non lineaires, et surtout l'AutoML de ML.NET qui automatise la recherche d'hyperparametres et la selection d'algorithme. Vous verrez aussi les dangers du surapprentissage et comment l'arreter precocement.

Le notebook 4 est le plus dense (82 cellules) et le plus crucial : evaluation rigoureuse. Vous apprendrez a mesurer un modele avec R², MAE, RMSE, a utiliser la validation croisee pour estimer la generalisation, et a expliquer les predictions avec la Permutation Feature Importance (PFI) et le Feature Contribution Calculation (FCC). Ce notebook transforme un "modele qui marche" en un modele que vous comprenez et pouvez justifier.

### Phase 2 : Fonctionnalites avances (ML-5 a ML-7, ~2h)

Le notebook 5 aborde les series temporelles avec `ForecastBySsa` (Singular Spectrum Analysis), un algorithme qui detecte automatiquement les tendances et saisonnalites. Vous travaillerez sur un dataset de ventes quotidiennes, apprendrez a detecter des anomalies par ecart a la moyenne mobile, a quantifier l'incertitude via les intervalles de confiance, et a comparer plusieurs configurations de prevision. Ce notebook est directement applicable a la prevision de ventes, de charge serveur, ou de demande produit.

Le notebook 6 presente l'interoperabilite ONNX — le pont entre l'ecosysteme Python et .NET. Vous apprendrez a charger des models exportes depuis scikit-learn ou PyTorch, a exporter un modele ML.NET vers ONNX, et meme a utiliser des modele Hugging Face (BERT, Whisper) via ONNX Runtime. Le notebook montre un workflow complet : R&D en Python, export ONNX, deploiement en production dans une application .NET. C'est le chapitre "deploiement en entreprise" du parcours.

Le notebook 7 explore les systemes de recommandation — un domaine ou ML.NET brille vraiment en production. Vous implémenterez la factorisation matricielle (collaborative filtering), apprendrez a genérer des recommendations Top-N, a mesurer la qualite avec Precision@K et NDCG, et a gerer le "cold start problem" (nouveaux utilisateurs ou items sans historique). Deux exemples concrets : recommandation de films et recommandation e-commerce.

### Phase 3 : TP Capstone (~1h)

Le TP final combine tout ce qui a ete appris. Il commence par une regression simple avec ML.NET pour predire des ventes d'assurance, puis introduit la regression bayesienne via Infer.NET pour quantifier l'incertitude des predictions. Ce notebook est le seul de la serie a utiliser Infer.NET (Microsoft's probabilistic programming language pour .NET) et fait le lien avec la serie [Probas/Infer](../../Probas/Infer/README.md).

## Exemples concrets

Derriere chaque concept de cette serie se cache une application reel :

- **Prediction de prix de taxi** (ML-1) : le dataset NYC taxi-fare est un benchmark classique pour la regression en production. Les memes techniques servent a estimer le prix d'un VLF, d'un cours de bourse, ou d'une commande de livraison.
- **Feature engineering de textes** (ML-2) : les transformations d'encodage de texte vues dans ce notebook sont les memes qu'utilisent les moteurs de recherche pour transformer du texte brut en features numeriques.
- **Prévision de ventes quotidiennes** (ML-5) : l'algorithme SSA detecte les cycles et saisonnalites dans les donnees de vente — applicable a la gestion de stock, la prevision de charge pour le cloud, ou l'anticipation de la demande produit.
- **Export ONNX de modeles Hugging Face** (ML-6) : servir un modele BERT d'analyse de sentiments ou un Whisper de transcription dans une application .NET d'entreprise, sans dependance Python. C'est exactement le scenario que rencontrent les equipes qui adoptent le ML sans migrer leur stack.
- **Recommandation de films** (ML-7) : la factorisation matricielle est le meme principe que celui derriere les recommendations Netflix, Amazon, ou Spotify — uniquement ici, tout tourne dans un process .NET.
- **Regression bayesienne pour les ventes** (TP) : combiner regression classique et inference bayesienne pour predire non seulement un chiffre, mais aussi la plage de confiance. Essentiel pour les decisions finance ou logistique ou l'incertitude a un cout reel.

## Prerequisites detailles

### Pour suivre cette serie

| Niveau | Connaissance | Pourquoi |
|--------|-------------|----------|
| **C# intermediaire** | Classes, generiques, LINQ, async/await | Les notebooks utilisent ces concepts pour construire les pipelines et definir les classes de donnees |
| **.NET SDK 9.0+** | dotnet CLI | Requirement pour .NET Interactive (kernel Jupyter) |
| **Jupyter** | Navigation basique dans un notebook | Les notebooks sont executes dans Jupyter / VS Code avec l'extension Polyglot Notebooks |

### Concepts ML utiles (non obligatoires)

Avoir une intuition de ces concepts aidera, mais ils sont **expliques dans les notebooks** :

- **Regression vs classification** : predire un nombre (prix) vs predire une categorie (spam/non-spam). Explique dans ML-1.
- **Overfitting** : un modele qui memorise les donnees d'entrainement mais echoue sur de nouvelles donnees. Aborde dans ML-3.
- **Cross-validation** : methodologie pour estimer la performance d'un modele sur des donnees non vues. Expliquee dans ML-4.
- **Features categorielles** : variables non-numeriques (couleur, pays, ville) qui doivent etre codees numeriquement. Vue dans ML-2.

### Parcours conseilles selon votre profil

| Profil | Parcours | Duree |
|--------|----------|-------|
| **Developpeur C# debutant en ML** | ML-1 → ML-2 → ML-3 → ML-4 → TP | ~2h30 |
| **Developpeur C# experimente** | ML-1 → ML-4 → ML-5 → ML-6 → ML-7 | ~2h |
| **Data scientist .NET enterprise** | ML-3 → ML-4 → ML-6 → ML-7 | ~2h |

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

| Fichier          | Description                                                  |
|------------------|--------------------------------------------------------------|
| `taxi-fare.csv`  | Donnees courses taxi NYC (fourni localement, exclu du depot) |

## Installation

```bash
# 1. Installer .NET SDK 9.0+
#    https://dotnet.microsoft.com/download
dotnet --version  # doit afficher 9.x.x

# 2. Installer .NET Interactive
dotnet tool install -g Microsoft.dotnet-interactive
dotnet interactive jupyter install

# 3. Verification
jupyter kernelspec list  # doit montrer .net-csharp
```

## Prerequisites

```bash
# Packages (installes via #r dans notebooks, pas de pip)
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

## FAQ / Troubleshooting

### .NET Interactive ne s'installe pas ou le kernel n'apparait pas

```bash
# Verifier que .NET SDK 9.0+ est installe
dotnet --version  # doit afficher 9.x.x

# Installer .NET Interactive globalement
dotnet tool install --global Microsoft.dotnet-interactive
dotnet interactive jupyter install

# Si deja installe mais kernel absent, mettre a jour
dotnet tool update --global Microsoft.dotnet-interactive
dotnet interactive jupyter install

# Verifier
jupyter kernelspec list  # doit montrer .net-csharp
```

Si `jupyter kernelspec list` ne montre pas `.net-csharp` apres installation, verifier que `dotnet` est dans le PATH et relancer le terminal.

### Erreur "No handler for trainer" dans ML-3

Certains trainers (LightGBM, SymSGD) necessitent des packages NuGet supplementaires. Dans le notebook :

```csharp
#r "nuget: Microsoft.ML.LightGbm"
```

Verifier dans ML-3 que tous les packages `#r "nuget:..."` du debut du notebook sont bien executes avant d'appeler le trainer.

### Le dataset taxi-fare.csv est introuvable

Le dataset doit se trouver dans le meme repertoire que le notebook. Verifier :

```csharp
// En debut de notebook, verifier le chemin
if (!File.Exists("taxi-fare.csv"))
    Console.WriteLine("taxi-fare.csv non trouve. Placer le fichier a cote du notebook.");
```

Le fichier `taxi-fare.csv` est fourni localement (exclu du depot via `.gitignore`). Placer le fichier dans le meme repertoire que les notebooks.

### Les metriques de ML-4 semblent aberrantes (R² negatif, MAE tres eleve)

Un R² negatif signifie que le modele predit **moins bien** que la moyenne constante. Causes courantes :

1. **Donnees non melangees** : `mlContext.Data.ShuffleRows()` avant le split
2. **Features non normalisees** : ajouter `NormalizeMinMax` ou `MeanVariance` au pipeline
3. **Split temporel** pour des donnees ordonnees : utiliser un split chronologique plutot que aleatoire

### ONNX export echoue avec "NotSupportedException" (ML-6)

Tous les trainers ML.NET ne supportent pas l'export ONNX. Les trainers compatibles incluent : FastTree, LightGBM, SDCA, Lbfgs. Les trainers **non compatibles** : les trainers de recommandation (MatrixFactorization) et certains trainers de series temporelles.

### Comment passer de scikit-learn a ML.NET ?

Les concepts se correspondent directement :

| Concept scikit-learn | Equivalent ML.NET |
| ---------------------- | ------------------- |
| `fit()` | `Fit()` sur le pipeline |
| `predict()` | `CreatePredictionEngine().Predict()` |
| `train_test_split()` | `mlContext.Data.TrainTestSplit()` |
| `cross_val_score()` | `mlContext.Regression.CrossValidate()` |
| Pipeline sklearn | `EstimatorChain` ML.NET |
| `OneHotEncoder` | `OneHotEncodingEstimator` |
| `StandardScaler` | `NormalizeMinMax` / `MeanVariance` |

## Ressources

- [Documentation ML.NET](https://docs.microsoft.com/en-us/dotnet/machine-learning/)
- [ML.NET Samples](https://github.com/dotnet/machinelearning-samples)
- [ML.NET API Reference](https://docs.microsoft.com/en-us/dotnet/api/microsoft.ml)
- [Hands-On AI Trading](https://www.hands-on-ai-trading.com/) — chapitres ML.NET et pipeline de trading

## Licence

Voir la licence du repository principal.

## Cross-series Bridges

| Serie | Lien | Connection |
|-------|------|------------|
| [Probas/Infer](../../Probas/Infer/README.md) | Regression bayesienne | Le TP capstone utilise Infer.NET, le meme moteur probabiliste de la serie Probas |
| [Search](../../Search/README.md) | Optimisation | L'AutoML (ML-3) et la detection de saisonnalite (ML-5) utilisent des techniques de recherche et optimisation |
| [QuantConnect](../../QuantConnect/README.md) | Trading algorithmique | Les modeles de prevision de series temporelles (ML-5) s'appliquent directement aux strategies de trading |
| [GenAI](../../GenAI/README.md) | IA generative | Les modeles ONNX (ML-6) servent a deployer des LLMs et modeles NLP (BERT, Whisper) via ONNX Runtime dans .NET |
| [DataScienceWithAgents](../DataScienceWithAgents/README.md) | Python ML | Les memes concepts ML.NET existent en Python via scikit-learn dans le track DataScienceWithAgents |

## Navigation

- [<- Notebooks ML](../README.md)
- [DataScienceWithAgents ->](../DataScienceWithAgents/README.md)

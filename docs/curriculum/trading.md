<!--
  FICHIER GENERE — ne pas editer a la main.
  Cette page de parcours est derivee du catalogue de notebooks par
  scripts/notebook_tools/generate_parcours.py, puis regeneree chaque jour
  sur `main` par .github/workflows/catalog-cron.yml. Toute edition manuelle
  sera silencieusement ecrasee au prochain passage du cron. Pour corriger
  une derive (comptes, enumerations), corriger la SOURCE (le catalogue /
  les metadonnees de notebook) ou le generateur — jamais cette page.
  Cf .claude/rules/catalog-pr-hygiene.md (les artefacts generes
  appartiennent a l'automatisation).
-->

# Trading Algorithmique

**QuantConnect, ML appliqué et probabilités**

Stratégies de trading algorithmique avec QuantConnect, pipeline ML (Transformer, DQN, LSTM), indicateurs techniques avancés, et modèles probabilistes. Du backtesting basique au reinforcement learning.

## Statistiques

| Métrique | Valeur |
|----------|--------|
| Notebooks | 240 |
| PRODUCTION | 0 |
| BETA | 223 |
| ALPHA | 17 |

## ML/DataScienceWithAgents (54 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [1.2 - Manipulation de Données avec NumPy](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-PythonForDataScience/notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb) | BETA | Oui |
| 2 | [1.3 - Analyse de Données avec Pandas](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-PythonForDataScience/notebooks/1.3-Analyse_de_Donnees_avec_Pandas.ipynb) | BETA | Oui |
| 3 | [2.1 — Le workflow d'apprentissage automatique](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.1-Workflow-ML.ipynb) | BETA | Oui |
| 4 | [2.10 — Optimisation d'hyperparamètres : grille, hasard,…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.10-Optimisation-Hyperparametres.ipynb) | BETA | Non |
| 5 | [2.11 — Régularisation sparse : LASSO (L1) vs Ridge…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.11-Regularisation-Sparse-LASSO.ipynb) | BETA | Oui |
| 6 | [2.12 — Données déséquilibrées : la courbe PR, les…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.12-Donnees-Desequilibrees.ipynb) | BETA | Oui |
| 7 | [2.13 — Analyse d'erreurs : diagnostiquer un modèle…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.13-Analyse-Erreurs.ipynb) | BETA | Oui |
| 8 | [2.2 — La descente de gradient : comment un modèle…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.2-Descente-de-gradient.ipynb) | BETA | Oui |
| 9 | [2.3 — Régression linéaire et régression logistique](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.3-Regression-lineaire-logistique.ipynb) | BETA | Oui |
| 10 | [Naive Bayes génératif vs régression logistique…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.3b-Naive-Bayes-Generatif.ipynb) | BETA | Oui |
| 11 | [Régression en grande dimension — quand p >> n : ridge,…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.3c-Regression-Grande-Dimension.ipynb) | BETA | Oui |
| 12 | [Modèle gaussien, frontière LDA / QDA](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.3d-Modele-Gaussien-LDA-QDA.ipynb) | BETA | Oui |
| 13 | [2.4 — Arbres de décision, forêts aléatoires et boosting](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.4-Arbres-Forets-Ensembles.ipynb) | BETA | Oui |
| 14 | [2.5 — Biais, variance, validation croisée et courbe ROC](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.5-Biais-Variance-CV-ROC.ipynb) | BETA | Oui |
| 15 | [2.5b — Calibration des probabilités : reliability…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.5b-Calibration-Probabilites.ipynb) | BETA | Oui |
| 16 | [2.5c — Equite par sous-groupe : compromis…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.5c-Equite-Sous-Groupes.ipynb) | BETA | Oui |
| 17 | [2.6 — Clustering (KMeans) et réduction de dimension…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.6-Clustering-KMeans-PCA.ipynb) | BETA | Oui |
| 18 | [2.7 — Modèles non paramétriques : SVM et k plus proches…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.7-Modeles-Non-Parametriques.ipynb) | BETA | Oui |
| 19 | [2.8 — Théorie de l'apprentissage : PAC et dimension de…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.8-Theorie-PAC.ipynb) | BETA | Oui |
| 20 | [2.8c — Borne + Témoin extrémal + Concentration : ce que…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.8c-Borne-Temoin-Concentration.ipynb) | BETA | Oui |
| 21 | [Novikoff : la convergence du perceptron, démontrée et…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.8d-Lean-Novikoff-Convergence.ipynb) | BETA | Oui |
| 22 | [2.9 — Grokking : la généralisation qui arrive en retard](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.9-Grokking-Generalisation.ipynb) | BETA | Oui |
| 23 | [3.0 — Théorie de l'information : entropie, KL,…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.0-Theorie-Information.ipynb) | BETA | Oui |
| 24 | [3.1 — La rétropropagation : la chaîne des gradients à…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.1-Retropropagation.ipynb) | BETA | Oui |
| 25 | [3.2 — Les optimisateurs : de SGD à Adam, ce qui change…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.2-Optimisateurs.ipynb) | BETA | Oui |
| 26 | [3.3 — Régularisation : dropout, weight decay, early…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.3-Regularisation.ipynb) | BETA | Oui |
| 27 | [3.4 — Attention et Transformer from scratch : jusqu'au…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.4-Attention-Transformer-From-Scratch.ipynb) | BETA | Oui |
| 28 | [3.5 — Grokking et double descente : quand la…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.5-Phenomenes-de-Generalisation.ipynb) | BETA | Oui |
| 29 | [3.6 — Modèles génératifs : trois objectifs, trois…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.6-Modeles-Generatifs.ipynb) | BETA | Oui |
| 30 | [3.6b — Modèles génératifs en PyTorch : VAE, GAN et…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.6b-Modeles-Generatifs-PyTorch.ipynb) | BETA | Oui |
| 31 | [3.7 — Distillation maître-élève : quand le savoir se…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.7-Distillation-Maitre-Eleve.ipynb) | BETA | Oui |
| 32 | [Représentations contrastives modernes — du skip-gram…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-DeepLearning/3.8-Representations-Contrastives.ipynb) | BETA | Oui |
| 33 | [4.1 — Le neurone convolutif from scratch : kernel…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/4.1-Conv-NumPy-Torch-Allclose.ipynb) | BETA | Oui |
| 34 | [4.2 — ConvNet profonde : pourquoi les résiduelles](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/4.2-ConvNet-Profonde-Residuelles.ipynb) | BETA | Non |
| 35 | [4.3 — Transfer learning : réutiliser un ResNet18…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/4.3-TransferLearning-ResNet.ipynb) | BETA | Non |
| 36 | [Lab 1 - Les Bases de la Data Science en Python](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track1-LangChain/Day1-Foundations/Labs/Lab1-PythonForDataScience.ipynb) | BETA | Oui |
| 37 | [Lab 2 - Analyser un Appel d'Offre avec l'IA](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track1-LangChain/Day2-Document-Agents/Labs/Lab2-RFP-Analysis/Lab2-RFP-Analysis.ipynb) | BETA | Non |
| 38 | [Lab 3 - Pré-qualifier des Candidats avec l'IA](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track1-LangChain/Day2-Document-Agents/Labs/Lab3-CV-Screening/Lab3-CV-Screening.ipynb) | BETA | Non |
| 39 | [Lab 4 - Le Nettoyage de Données avec Pandas](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track1-LangChain/Day3-Data-Agents/Labs/Lab4-DataWrangling/Lab4-DataWrangling.ipynb) | BETA | Oui |
| 40 | [Lab 5 - De la Visualisation au Machine Learning](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track1-LangChain/Day3-Data-Agents/Labs/Lab5-Viz-ML/Lab5-Viz-ML.ipynb) | BETA | Oui |
| 41 | [Lab 6 - Anatomie de votre premier Agent d'IA](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track1-LangChain/Day3-Data-Agents/Labs/Lab6-First-Agent/Lab6-First-Agent.ipynb) | ALPHA | Non |
| 42 | [Lab 7 - Votre premier Agent Analyste de Données](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track1-LangChain/Day3-Data-Agents/Labs/Lab7-Data-Analysis-Agent/Lab7-Data-Analysis-Agent.ipynb) | BETA | Non |
| 43 | [Lab 8: Introduction au Framework ADK et Multi-Provider](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day4-Foundations/Lab8-ADK-Introduction.ipynb) | BETA | Non |
| 44 | [Lab 9: Premier Agent ADK pour Data Science](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day4-Foundations/Lab9-First-ADK-Agent.ipynb) | BETA | Oui |
| 45 | [Lab 10: Data File Analyzer (DS-STAR Component)](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day5-DS-Star/Lab10-File-Analyzer.ipynb) | BETA | Oui |
| 46 | [Lab 11: Planner-Coder-Verifier Loop (DS-STAR Core)](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day5-DS-Star/Lab11-Planner-Coder-Loop.ipynb) | ALPHA | Oui |
| 47 | [Lab 12: DS-STAR Workshop - Analyse Multi-Fichiers](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day5-DS-Star/Lab12-DS-Star-Workshop.ipynb) | BETA | Oui |
| 48 | [Lab 14 : Tracabilite de la consommation — le contrat C6…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day5-DS-Star/Lab14-Token-Usage.ipynb) | BETA | Non |
| 49 | [Lab 18: Persistance d'etat de session - une…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day5-DS-Star/Lab18-Session-Persistence.ipynb) | BETA | Non |
| 50 | [Lab 13: Web Search pour Modèles SOTA (MLE-STAR…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day6-MLE-Star/Lab13-Web-Search-SOTA.ipynb) | BETA | Oui |
| 51 | [Lab 14: Ablation et Raffinement Ciblé (MLE-STAR…](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day6-MLE-Star/Lab14-Ablation-Refinement.ipynb) | ALPHA | Oui |
| 52 | [Lab 15: Kaggle Challenge avec MLE-STAR](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day6-MLE-Star/Lab15-Kaggle-Challenge.ipynb) | BETA | Oui |
| 53 | [Lab 16: Data Science Agent avec GCP BigQuery](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day7-Production/Lab16-Data-Science-Agent.ipynb) | ALPHA | Oui |
| 54 | [Lab 17: Projet Final - Pipeline DS-STAR Complet](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day7-Production/Lab17-Final-Project.ipynb) | ALPHA | Oui |

## ML/ML.Net (23 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [ML-1 (Python) : Introduction au Machine Learning avec…](../../MyIA.AI.Notebooks/ML/ML.Net/ML-1-Introduction-Python.ipynb) | BETA | Oui |
| 2 | [ML-1 : Introduction au Machine Learning avec ML.NET](../../MyIA.AI.Notebooks/ML/ML.Net/ML-1-Introduction.ipynb) | BETA | Oui |
| 3 | [ML-10 (Python) : l'illusion de progression en détection…](../../MyIA.AI.Notebooks/ML/ML.Net/ML-10-TSAD-Benchmark-Flaws-Python.ipynb) | BETA | Oui |
| 4 | [ML-11 : le Matrix Profile multidimensionnel, une…](../../MyIA.AI.Notebooks/ML/ML.Net/ML-11-MatrixProfile-Multidim-Python.ipynb) | BETA | Oui |
| 5 | [ML-2 : Préparation des données et ingénierie des…](../../MyIA.AI.Notebooks/ML/ML.Net/ML-2-Data%26Features-Python.ipynb) | BETA | Oui |
| 6 | [ML-2 : Préparation des données et ingénierie des…](../../MyIA.AI.Notebooks/ML/ML.Net/ML-2-Data%26Features.ipynb) | BETA | Oui |
| 7 | [ML-3 : Entraînement et AutoML](../../MyIA.AI.Notebooks/ML/ML.Net/ML-3-Entrainement%26AutoML.ipynb) | BETA | Oui |
| 8 | [ML-3 (Python) : Entraînement et AutoML](../../MyIA.AI.Notebooks/ML/ML.Net/ML-3-Entrainement-Python.ipynb) | BETA | Oui |
| 9 | [ML-4 : Évaluation des modèles (Python / sklearn)](../../MyIA.AI.Notebooks/ML/ML.Net/ML-4-Evaluation-Python.ipynb) | BETA | Oui |
| 10 | [ML-4 : Evaluation des modèles](../../MyIA.AI.Notebooks/ML/ML.Net/ML-4-Evaluation.ipynb) | BETA | Oui |
| 11 | [ML-4b : Validité statistique des comparaisons de…](../../MyIA.AI.Notebooks/ML/ML.Net/ML-4b-ModelComparison-Validity-Python.ipynb) | BETA | Oui |
| 12 | [ML-5 (Python) : Prévision de séries temporelles (STL +…](../../MyIA.AI.Notebooks/ML/ML.Net/ML-5-TimeSeries-Python.ipynb) | BETA | Oui |
| 13 | [ML-5 : Time Series Forecasting avec ML.NET](../../MyIA.AI.Notebooks/ML/ML.Net/ML-5-TimeSeries.ipynb) | BETA | Oui |
| 14 | [ML-5b (Python) : Séries temporelles classiques —…](../../MyIA.AI.Notebooks/ML/ML.Net/ML-5b-Series-Temporelles-Classiques-Python.ipynb) | BETA | Oui |
| 15 | [ML-6 (Python) : Intégration de modèles ONNX (skl2onnx +…](../../MyIA.AI.Notebooks/ML/ML.Net/ML-6-ONNX-Python.ipynb) | BETA | Oui |
| 16 | [ML-6 : ONNX Model Integration avec ML.NET](../../MyIA.AI.Notebooks/ML/ML.Net/ML-6-ONNX.ipynb) | BETA | Oui |
| 17 | [ML-7 (Python) : Systèmes de recommandation par…](../../MyIA.AI.Notebooks/ML/ML.Net/ML-7-Recommendation-Python.ipynb) | BETA | Oui |
| 18 | [ML-7 : Systèmes de Recommandation avec ML.NET](../../MyIA.AI.Notebooks/ML/ML.Net/ML-7-Recommendation.ipynb) | BETA | Oui |
| 19 | [ML-8 (Python) : Clustering non-supervisé avec K-Means](../../MyIA.AI.Notebooks/ML/ML.Net/ML-8-Clustering-Python.ipynb) | BETA | Oui |
| 20 | [ML-8 : Clustering non-supervise avec K-Means](../../MyIA.AI.Notebooks/ML/ML.Net/ML-8-Clustering.ipynb) | BETA | Oui |
| 21 | [ML-9 (Python) : Détection d'anomalies par PCA (erreur…](../../MyIA.AI.Notebooks/ML/ML.Net/ML-9-Anomaly-Detection-Python.ipynb) | BETA | Oui |
| 22 | [ML-9 : Detection d'anomalies avec Randomized PCA](../../MyIA.AI.Notebooks/ML/ML.Net/ML-9-Anomaly-Detection.ipynb) | BETA | Oui |
| 23 | [TP : Prevision des ventes d'assurance](../../MyIA.AI.Notebooks/ML/ML.Net/TP-prevision-ventes.ipynb) | BETA | Oui |

## Probas (2 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [Infer-101 : Introduction a Infer.NET](../../MyIA.AI.Notebooks/Probas/Infer-101.ipynb) | BETA | Oui |
| 2 | [Le Framework Rational Speech Act (RSA)](../../MyIA.AI.Notebooks/Probas/Pyro_RSA_Hyperbole.ipynb) | BETA | Oui |

## Probas/DecisionTheory (26 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [Du graphe causal au do-calculus — le pont entre les…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/Do-Calculus-Bridge.ipynb) | BETA | Oui |
| 2 | [DoWhy-1 — Exiger un estimand : l'identification causale…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/DoWhy-1-Estimand-et-Intervention.ipynb) | BETA | Oui |
| 3 | [DoWhy-2 — Le contrefactuel individuel : quand l'effet…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/DoWhy-2-Contrefactuel-Individuel.ipynb) | BETA | Oui |
| 4 | [Méthodes quasi-expérimentales — identifier l'effet…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/Quasi-Experimental.ipynb) | BETA | Oui |
| 5 | [DecInfer-01-Utility-Foundations : Axiomes et Fondements](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-01-Utility-Foundations.ipynb) | BETA | Oui |
| 6 | [DecInfer-02-Théorème de représentation de von…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-02-Lean-ExpectedUtility.ipynb) | BETA | Oui |
| 7 | [DecInfer-03-Utility-Money : Utilite de l'Argent et…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-03-Utility-Money.ipynb) | BETA | Oui |
| 8 | [DecInfer-04-Multi-Attribute : Utilite Multi-Attributs](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-04-Multi-Attribute.ipynb) | BETA | Oui |
| 9 | [DecInfer-05-Decision-Networks : Reseaux de Decision](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-05-Decision-Networks.ipynb) | BETA | Oui |
| 10 | [DecInfer-06-Value-Information : Valeur de l'Information](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-06-Value-Information.ipynb) | BETA | Oui |
| 11 | [DecInfer-07-Expert-Systems : Decisions Robustes et…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-07-Expert-Systems.ipynb) | BETA | Oui |
| 12 | [DecInfer-08-Sequential : MDPs, Bandits et POMDPs](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-08-Sequential.ipynb) | BETA | Oui |
| 13 | [DecInfer-09-Preuves formelles — Indice de Gittins](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-09-Lean-Gittins.ipynb) | BETA | Oui |
| 14 | [DecInfer-10-Thompson-Sampling : Bandits bayesiens par…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-10-Thompson-Sampling.ipynb) | BETA | Oui |
| 15 | [DecPyMC-1-Utility-Foundations : Axiomes et Fondements](../../MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-1-Utility-Foundations.ipynb) | BETA | Oui |
| 16 | [DecPyMC-10 : Ruine et capital — le processus de…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-10-Ruine-Lundberg.ipynb) | BETA | Oui |
| 17 | [DecPyMC-11 — Valeur de l'Information en Souscription](../../MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-11-Valeur-Info-Souscription.ipynb) | BETA | Oui |
| 18 | [DecPyMC-12 — Fréquence × sévérité hiérarchique : le…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-12-Freq-Sev-Hierarchique.ipynb) | BETA | Oui |
| 19 | [DecPyMC-2-Utility-Money : Utilite de l'Argent et…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-2-Utility-Money.ipynb) | BETA | Oui |
| 20 | [DecPyMC-3-Multi-Attribute : Utilite Multi-Attributs](../../MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-3-Multi-Attribute.ipynb) | BETA | Oui |
| 21 | [DecPyMC-4-Decision-Networks : Reseaux de Decision](../../MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-4-Decision-Networks.ipynb) | BETA | Oui |
| 22 | [DecPyMC-5-Valeur de l'Information](../../MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-5-Value-Information.ipynb) | BETA | Oui |
| 23 | [DecPyMC-6-Systèmes Experts et Decisions Robustes](../../MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-6-Expert-Systems.ipynb) | BETA | Oui |
| 24 | [DecPyMC-7-MDPs, Bandits et POMDPs](../../MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-7-Sequential.ipynb) | BETA | Oui |
| 25 | [DecPyMC-8 — Crédibilité actuarielle de Bühlmann–Straub…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-8-Actuarial-Credibility.ipynb) | BETA | Oui |
| 26 | [DecPyMC-9 : Du risque à la prime — prime pure,…](../../MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-9-Prime-Pure-Chargement.ipynb) | BETA | Oui |

## Probas/Infer (20 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [Infer-1-Setup : Introduction et Installation](../../MyIA.AI.Notebooks/Probas/Infer/Infer-1-Setup.ipynb) | BETA | Oui |
| 2 | [Infer-10-Model-Sélection : Sélection et Comparaison de…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-10-Model-Selection.ipynb) | BETA | Oui |
| 3 | [Infer-11-Topic-Models : Latent Dirichlet Allocation…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-11-Topic-Models.ipynb) | BETA | Oui |
| 4 | [12. Modèles Hiérarchiques Bayésiens — Pooling Partiel…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-12-Modeles-Hierarchiques.ipynb) | BETA | Oui |
| 5 | [Infer-13-Crowdsourcing : Agregation de Labels et…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-13-Crowdsourcing.ipynb) | BETA | Oui |
| 6 | [Infer-14-Sequences : Hidden Markov Models et Series…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-14-Sequences.ipynb) | BETA | Oui |
| 7 | [Infer-15-Recommenders : systèmes de Recommandation](../../MyIA.AI.Notebooks/Probas/Infer/Infer-15-Recommenders.ipynb) | BETA | Oui |
| 8 | [Infer-16-Sparse-Gaussian-Process : Processus Gaussiens…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-16-Sparse-Gaussian-Process.ipynb) | BETA | Oui |
| 9 | [Infer-17 — Filtre de Kalman : systèmes dynamiques…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-17-Kalman-Filter.ipynb) | BETA | Oui |
| 10 | [Infer-18 — Détection de Rupture (Change-Point) :…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-18-Change-Point.ipynb) | BETA | Oui |
| 11 | [Infer-19 — Analyse de survie / fiabilite bayesienne :…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-19-Survival-Analysis.ipynb) | BETA | Oui |
| 12 | [Infer-2-Gaussian-Mixtures : Distributions Gaussiennes…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-2-Gaussian-Mixtures.ipynb) | BETA | Oui |
| 13 | [Infer-20 — Quotients, fibres et recollement : ce qui…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-20-Quotients-et-Fibres.ipynb) | BETA | Oui |
| 14 | [Infer-2b-Debugging-Bonnes-Pratiques : Troubleshooting…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-2b-Debugging-Bonnes-Pratiques.ipynb) | BETA | Oui |
| 15 | [Infer-3-Factor-Graphs : Graphes de Facteurs et…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-3-Factor-Graphs.ipynb) | BETA | Oui |
| 16 | [Infer-4-Bayesian-Networks : Reseaux Bayesiens…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-4-Bayesian-Networks.ipynb) | BETA | Oui |
| 17 | [Infer-5-Causal-Inference : Inférence Causale et…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-5-Causal-Inference.ipynb) | BETA | Oui |
| 18 | [Infer-7-Skills-IRT : Evaluation de Competences et…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-7-Skills-IRT.ipynb) | BETA | Oui |
| 19 | [Infer-8-TrueSkill : Système de Classement et…](../../MyIA.AI.Notebooks/Probas/Infer/Infer-8-TrueSkill.ipynb) | BETA | Oui |
| 20 | [Infer-9-Classification : Classification Bayesienne](../../MyIA.AI.Notebooks/Probas/Infer/Infer-9-Classification.ipynb) | BETA | Oui |

## Probas/PyMC (19 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [PyMC-1 : Configuration et Premier Modèle](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-01-Setup.ipynb) | BETA | Oui |
| 2 | [PyMC-2 : Distributions Gaussiennes et Mélanges](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-02-Gaussian-Mixtures.ipynb) | BETA | Oui |
| 3 | [PyMC-3 : Graphes de Facteurs et Inference Discrete](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-03-Factor-Graphs.ipynb) | BETA | Oui |
| 4 | [PyMC-4 : Reseaux Bayesiens](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-04-Bayesian-Networks.ipynb) | BETA | Oui |
| 5 | [PyMC-05-Causal-Inference : Inference Causale et…](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-05-Causal-Inference.ipynb) | BETA | Oui |
| 6 | [PyMC-06-Debugging : Troubleshooting et Bonnes Pratiques](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-06-Debugging.ipynb) | BETA | Oui |
| 7 | [PyMC-7 : Modèles de Competences (IRT et DINA)](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-07-Skills-IRT.ipynb) | BETA | Oui |
| 8 | [PyMC-8 : TrueSkill - Classement et Apprentissage en…](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-08-TrueSkill.ipynb) | BETA | Oui |
| 9 | [PyMC-9 : Classification Bayesienne et Tests A/B](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-09-Classification.ipynb) | BETA | Oui |
| 10 | [PyMC-10 : Sélection de Modèles et Comparaison…](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-10-Model-Selection.ipynb) | BETA | Oui |
| 11 | [PyMC-11 : Modèles de Sujets (Topic Models) et LDA](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-11-Topic-Models.ipynb) | BETA | Oui |
| 12 | [12. Modèles Hiérarchiques Bayesiens -- Pooling Partiel…](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-12-Modeles-Hierarchiques.ipynb) | BETA | Oui |
| 13 | [PyMC-13 : Crowdsourcing - Agregation de Labels et…](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-13-Crowdsourcing.ipynb) | BETA | Oui |
| 14 | [PyMC-14 — Modèles de Sequences et Chaînes de Markov…](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-14-Sequences.ipynb) | BETA | Oui |
| 15 | [PyMC-15-Recommenders : Systèmes de Recommandation…](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-15-Recommenders.ipynb) | BETA | Oui |
| 16 | [PyMC-16 : Processus Gaussiens et frontières non…](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-16-Sparse-Gaussian-Process.ipynb) | BETA | Oui |
| 17 | [17. Filtre de Kalman : systèmes dynamiques lineaires…](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-17-Kalman-Filter.ipynb) | BETA | Oui |
| 18 | [18. Detection de Rupture (Change-Point) : inferer le…](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-18-Change-Point.ipynb) | BETA | Oui |
| 19 | [19. Analyse de survie / fiabilite bayesienne : inferer…](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-19-Survival-Analysis.ipynb) | BETA | Oui |

## QuantConnect/ML-Training-Pipeline (1 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [M16 — HAR asymétrique débiaisé : le signal survit-il…](../../MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/m3_har_asymmetric_semivariance.ipynb) | BETA | Non |

## QuantConnect/Python (47 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [QC-Py-01 : Configuration et Premier Backtest…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-01-Setup.ipynb) | BETA | Non |
| 2 | [QC-Py-02 : QuantConnect Platform Fundamentals -…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-02-Platform-Fundamentals.ipynb) | BETA | Non |
| 3 | [QC-Py-03 - Data Management in QuantConnect](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-03-Data-Management.ipynb) | BETA | Non |
| 4 | [Objectifs d'Apprentissage](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-04-Research-Workflow.ipynb) | BETA | Non |
| 5 | [Objectifs d'Apprentissage](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-05-Universe-Selection.ipynb) | BETA | Non |
| 6 | [QC-Py-06 : Options Trading dans QuantConnect](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-06-Options-Trading.ipynb) | BETA | Non |
| 7 | [QC-Py-07 : Futures et Forex Trading dans QuantConnect](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-07-Futures-Forex.ipynb) | BETA | Non |
| 8 | [QC-Py-08 - Multi-Asset Portfolio Stratégies](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-08-Multi-Asset-Strategies.ipynb) | BETA | Non |
| 9 | [QC-Py-09 : Types d'Ordres et Order Management dans…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-09-Order-Types.ipynb) | BETA | Non |
| 10 | [Objectifs d'Apprentissage](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-10-Risk-Portfolio-Management.ipynb) | BETA | Non |
| 11 | [QC-Py-11 - Indicateurs Techniques dans QuantConnect](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-11-Technical-Indicators.ipynb) | BETA | Non |
| 12 | [QC-Py-12 - Backtesting et Analyse de Performance](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-12-Backtesting-Analysis.ipynb) | BETA | Non |
| 13 | [QC-Py-12b - Validité du backtest et signification…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-12b-Backtest-Validity.ipynb) | BETA | Non |
| 14 | [QC-Py-13 - Alpha Models et Algorithm Framework](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-13-Alpha-Models.ipynb) | BETA | Non |
| 15 | [QC-Py-14 - Portfolio Construction et Exécution Models](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-14-Portfolio-Construction-Execution.ipynb) | BETA | Non |
| 16 | [Objectifs d'Apprentissage](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-15-Parameter-Optimization.ipynb) | BETA | Non |
| 17 | [QC-Py-16 - Alternative Data dans QuantConnect](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-16-Alternative-Data.ipynb) | BETA | Non |
| 18 | [Objectifs d'Apprentissage](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-17-Sentiment-Analysis.ipynb) | BETA | Non |
| 19 | [QC-Py-18 - Feature Engineering pour Machine Learning…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-18-ML-Features-Engineering.ipynb) | ALPHA | Non |
| 20 | [Objectifs d'Apprentissage](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-19-ML-Supervised-Classification.ipynb) | BETA | Non |
| 21 | [Objectifs d'Apprentissage](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-20-ML-Regression-Prediction.ipynb) | BETA | Non |
| 22 | [QC-Py-21 - Portfolio Optimization avec Machine Learning](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-21-Portfolio-Optimization-ML.ipynb) | BETA | Non |
| 23 | [Objectifs d'Apprentissage](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-22-Deep-Learning-LSTM.ipynb) | BETA | Non |
| 24 | [QC-Py-23 — State Space Models pour Séries Temporelles…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-23-State-Space-Models.ipynb) | BETA | Non |
| 25 | [QC-Py-23b - PatchTST et iTransformer pour Prevision…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-23b-PatchTST-iTransformer.ipynb) | BETA | Non |
| 26 | [QC-Py-24 - Modèles Génératifs pour Anomaly Detection et…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-24-Autoencoders-Anomaly.ipynb) | BETA | Non |
| 27 | [Objectifs d'Apprentissage](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-25-Reinforcement-Learning.ipynb) | BETA | Non |
| 28 | [Objectifs d'Apprentissage](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-26-LLM-Trading-Signals.ipynb) | BETA | Non |
| 29 | [QC-Py-27 - Production Deployment](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-27-Production-Deployment.ipynb) | BETA | Non |
| 30 | [QC-Py-28 - Market Regime Detection](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-28-Market-Regime-Detection.ipynb) | BETA | Non |
| 31 | [QC-Py-30 - LSTM Training Multi-Asset (GPU)](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-30-LSTM-Training.ipynb) | BETA | Non |
| 32 | [QC-Py-31 - Transformer Encoder Multi-Asset (GPU)](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-31-Transformer-Training.ipynb) | ALPHA | Non |
| 33 | [QC-Py-32 - Reinforcement Learning DQN pour le Trading](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-32-RL-DQN-Trading.ipynb) | BETA | Non |
| 34 | [QC-Py-33 - Reinforcement Learning PPO pour le Trading](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-33-RL-PPO-Trading.ipynb) | BETA | Non |
| 35 | [QC-Py-34 - SAC et A2C : Comparaison d'Agents RL pour le…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-34-RL-SAC-A2C-Trading.ipynb) | BETA | Non |
| 36 | [QC-Py-35 - Reinforcement Learning pour la Construction…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-35-RL-Portfolio-Construction.ipynb) | ALPHA | Non |
| 37 | [QC-Py-40 : Paper Trading Binance - Mean Reversion…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-40-PaperTrading-Binance.ipynb) | BETA | Non |
| 38 | [QC-Py-41 : Paper Trading IBKR - SP500 Momentum](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-41-PaperTrading-IBKR.ipynb) | BETA | Non |
| 39 | [QC-Py-Cloud-01 : Analyse de Sentiment FinBERT sur QC…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-01-FinBERT-Sentiment.ipynb) | ALPHA | Non |
| 40 | [QC-Py-Cloud-02 : Classification de Texte et Sentiment…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-02-ML-Classification.ipynb) | ALPHA | Non |
| 41 | [QC-Py-Cloud-03 : Parite de Risque (Risk Parity)](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-03-Risk-Parity.ipynb) | BETA | Non |
| 42 | [QC-Py-Cloud-05 : Prevision par Reseau de Neurones (MLP)](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-05-MLP-Forecasting.ipynb) | ALPHA | Non |
| 43 | [Value Factor Z-Score — Sélection multi-facteurs…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-08-ValueFactor-ZScore.ipynb) | BETA | Non |
| 44 | [Option Wheel — Le paradoxe du win-rate eleve](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-09-OptionWheel.ipynb) | BETA | Non |
| 45 | [QC-Py-Cloud-10 : Reinforcement Learning - DQN Trading](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-10-RL-DQN-Trading.ipynb) | ALPHA | Non |
| 46 | [QC-Py-Cloud-14 — Dual Momentum : Asset Sélection…](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-14-DualMomentum.ipynb) | BETA | Non |
| 47 | [Workflow : Téléchargement et gestion des datasets](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Dataset-Workflow.ipynb) | ALPHA | Non |

## QuantConnect/kelly_lean (2 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [Le critere de Kelly — compagnon Python du lake…](../../MyIA.AI.Notebooks/QuantConnect/kelly_lean/Kelly_companion.ipynb) | BETA | Non |
| 2 | [Kelly — compagnon natif (kernel Lean 4)](../../MyIA.AI.Notebooks/QuantConnect/kelly_lean/Kelly_companion_lean.ipynb) | BETA | Non |

## QuantConnect/projects (46 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | [Research QuantBook: Adaptive Asset Allocation](../../MyIA.AI.Notebooks/QuantConnect/projects/AdaptiveAssetAllocation/quantbook.ipynb) | BETA | Non |
| 2 | [Research QuantBook: All-Weather Portfolio](../../MyIA.AI.Notebooks/QuantConnect/projects/AllWeather/quantbook.ipynb) | BETA | Non |
| 3 | [Alpha Correlation Analysis](../../MyIA.AI.Notebooks/QuantConnect/projects/Alpha-Correlation-Analysis/quantbook.ipynb) | BETA | Non |
| 4 | [Research QuantBook: BTC ML Enhanced](../../MyIA.AI.Notebooks/QuantConnect/projects/BTC-ML/quantbook.ipynb) | BETA | Non |
| 5 | [Research QuantBook: Multi-Channel ZigZag Crypto](../../MyIA.AI.Notebooks/QuantConnect/projects/Crypto-MultiCanal/quantbook.ipynb) | BETA | Non |
| 6 | [Research QuantBook: Deep Learning LSTM pour SPY](../../MyIA.AI.Notebooks/QuantConnect/projects/DL-LSTM/quantbook.ipynb) | BETA | Non |
| 7 | [Research QuantBook: DualMomentum (Antonacci)](../../MyIA.AI.Notebooks/QuantConnect/projects/DualMomentum/quantbook.ipynb) | BETA | Non |
| 8 | [Research QuantBook: Dual Momentum No TLT](../../MyIA.AI.Notebooks/QuantConnect/projects/DualMomentumNoTLT/quantbook.ipynb) | BETA | Non |
| 9 | [Research QuantBook: EMA-Cross Alpha Model](../../MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Alpha/quantbook.ipynb) | BETA | Non |
| 10 | [Research QuantBook: EMA Cross Equity](../../MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Crypto/quantbook.ipynb) | BETA | Non |
| 11 | [Research QuantBook: EMA Crossover SPY Index](../../MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Index/quantbook.ipynb) | BETA | Non |
| 12 | [Research QuantBook: Multi-Stock EMA Crossover](../../MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Stocks/quantbook.ipynb) | BETA | Non |
| 13 | [Research QuantBook: ETF Pairs Trading](../../MyIA.AI.Notebooks/QuantConnect/projects/ETF-Pairs/quantbook.ipynb) | BETA | Non |
| 14 | [Research QuantBook: Fama-French Factor ETF Rotation](../../MyIA.AI.Notebooks/QuantConnect/projects/FamaFrench/quantbook.ipynb) | BETA | Non |
| 15 | [Research QuantBook: ForexCarry (G10 FX Momentum)](../../MyIA.AI.Notebooks/QuantConnect/projects/ForexCarry/quantbook.ipynb) | BETA | Non |
| 16 | [Research QuantBook: Framework Composite EMA-Trend](../../MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_EMATrend/quantbook.ipynb) | BETA | Non |
| 17 | [Research QuantBook: Framework Composite FamaFrench +…](../../MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_FamaFrenchAllWeather/quantbook.ipynb) | BETA | Non |
| 18 | [Research QuantBook: Framework Composite Momentum +…](../../MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_MomentumRegime/quantbook.ipynb) | BETA | Non |
| 19 | [Framework Composite TrendWeather - Research](../../MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_TrendWeather/quantbook.ipynb) | BETA | Non |
| 20 | [Research QuantBook: FuturesTrend (Donchian Breakout)](../../MyIA.AI.Notebooks/QuantConnect/projects/FuturesTrend/quantbook.ipynb) | BETA | Non |
| 21 | [Research QuantBook: ML Classification (RandomForest)](../../MyIA.AI.Notebooks/QuantConnect/projects/ML-Classification/quantbook.ipynb) | BETA | Non |
| 22 | [ML Deep Learning - LSTM/GRU pour Trading](../../MyIA.AI.Notebooks/QuantConnect/projects/ML-DeepLearning/quantbook.ipynb) | ALPHA | Non |
| 23 | [Research QuantBook: ML-Enhanced Pairs Trading](../../MyIA.AI.Notebooks/QuantConnect/projects/ML-EnhancedPairs/quantbook.ipynb) | BETA | Non |
| 24 | [Research QuantBook: ML Ensemble](../../MyIA.AI.Notebooks/QuantConnect/projects/ML-Ensemble/quantbook.ipynb) | BETA | Non |
| 25 | [Research QuantBook: ML Feature Engineering](../../MyIA.AI.Notebooks/QuantConnect/projects/ML-FeatureEngineering/quantbook.ipynb) | BETA | Non |
| 26 | [ML Random Forest - Classification pour Trading](../../MyIA.AI.Notebooks/QuantConnect/projects/ML-RandomForest/quantbook.ipynb) | ALPHA | Non |
| 27 | [Research QuantBook: ML Regression](../../MyIA.AI.Notebooks/QuantConnect/projects/ML-Regression/quantbook.ipynb) | BETA | Non |
| 28 | [ML SVM - Support Vector Machine pour Trading](../../MyIA.AI.Notebooks/QuantConnect/projects/ML-SVM/quantbook.ipynb) | ALPHA | Non |
| 29 | [ML Text Classification for Trading](../../MyIA.AI.Notebooks/QuantConnect/projects/ML-TextClassification/quantbook.ipynb) | ALPHA | Non |
| 30 | [ML XGBoost - Gradient Boosting pour Trading](../../MyIA.AI.Notebooks/QuantConnect/projects/ML-XGBoost/quantbook.ipynb) | BETA | Non |
| 31 | [Research QuantBook: Mean Reversion (Sector ETFs)](../../MyIA.AI.Notebooks/QuantConnect/projects/MeanReversion/quantbook.ipynb) | BETA | Non |
| 32 | [Research QuantBook: MomentumStrategy (Sector ETF…](../../MyIA.AI.Notebooks/QuantConnect/projects/MomentumStrategy/quantbook.ipynb) | BETA | Non |
| 33 | [Research QuantBook: Equity Multi-Layer EMA + ML Filters](../../MyIA.AI.Notebooks/QuantConnect/projects/Multi-Layer-EMA/quantbook.ipynb) | BETA | Non |
| 34 | [Research QuantBook: Option Wheel Strategy](../../MyIA.AI.Notebooks/QuantConnect/projects/Option-Wheel/quantbook.ipynb) | BETA | Non |
| 35 | [Research QuantBook: Options Wheel Tech Stocks](../../MyIA.AI.Notebooks/QuantConnect/projects/Options-VGT/quantbook.ipynb) | BETA | Non |
| 36 | [Research QuantBook: Covered Call Strategy](../../MyIA.AI.Notebooks/QuantConnect/projects/OptionsIncome/quantbook.ipynb) | BETA | Non |
| 37 | [Research QuantBook: PairsTrading (Statistical…](../../MyIA.AI.Notebooks/QuantConnect/projects/PairsTrading/quantbook.ipynb) | BETA | Non |
| 38 | [Research QuantBook: RL Portfolio Allocation](../../MyIA.AI.Notebooks/QuantConnect/projects/RL-Portfolio/quantbook.ipynb) | BETA | Non |
| 39 | [Research QuantBook: RegimeSwitching Alpha Model](../../MyIA.AI.Notebooks/QuantConnect/projects/RegimeSwitching/quantbook.ipynb) | BETA | Non |
| 40 | [Research QuantBook: RiskParity (Inverse-Volatility…](../../MyIA.AI.Notebooks/QuantConnect/projects/RiskParity/quantbook.ipynb) | BETA | Non |
| 41 | [Research QuantBook: Sector-Momentum (Dual Momentum)](../../MyIA.AI.Notebooks/QuantConnect/projects/SectorMomentum/quantbook.ipynb) | BETA | Non |
| 42 | [Research QuantBook: Trend Following Competition](../../MyIA.AI.Notebooks/QuantConnect/projects/Trend-Following/quantbook.ipynb) | BETA | Non |
| 43 | [Research QuantBook: TrendStocks Alpha Model](../../MyIA.AI.Notebooks/QuantConnect/projects/TrendStocks-Alpha/quantbook.ipynb) | BETA | Non |
| 44 | [Research QuantBook: TurnOfMonth (Calendar Anomaly)](../../MyIA.AI.Notebooks/QuantConnect/projects/TurnOfMonth/quantbook.ipynb) | BETA | Non |
| 45 | [Research QuantBook: VIX-TermStructure (Short Volatility…](../../MyIA.AI.Notebooks/QuantConnect/projects/VIX-TermStructure/quantbook.ipynb) | BETA | Non |
| 46 | [Top-4 Sharpe > 0.5 Stratégies: OOS Deep-Dive (Issue…](../../MyIA.AI.Notebooks/QuantConnect/projects/_docs/qc_top4_oos_extension.ipynb) | BETA | Non |

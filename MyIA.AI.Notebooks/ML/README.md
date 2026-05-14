# ML - Machine Learning

<!-- CATALOG-STATUS
series: ML
pedagogical_count: 30
breakdown: DataScienceWithAgents=22, ML.Net=8
maturity: BETA=18, ALPHA=9, PRODUCTION=2, DRAFT=1
-->

Vous êtes développeur ou analyste et vous voulez construire des modèles prédictifs sans devenir data scientist théoricien ? Cette série vous forme au Machine Learning pratique avec deux stack complémentaires : **ML.NET** pour l'écosystème .NET/C# (8 notebooks, ~6h) et **Python Data Science with Agents** pour les pipelines modernes enrichis de LLMs (22 notebooks, ~20h). À la fin, vous saurez charger des données, entraîner un modèle, l'évaluer rigoureusement, et le déployer en production.

## Parcours d'apprentissage

### Track A : ML.NET (.NET/C#, 8 notebooks, ~6h)

Le parcours ML.NET couvre le pipeline complet en C# : les notebooks 1-2 introduisent ML.NET et la préparation de données (IDataView, encodage). Le notebook 3 couvre l'entraînement (SDCA, LightGBM, AutoML). Le notebook 4 est crucial : évaluation rigoureuse par cross-validation et Permutation Feature Importance. Les notebooks 5-7 abordent les séries temporelles, l'export ONNX pour la production, et les systèmes de recommandation. Le TP final (prévision de ventes) combine ML.NET et Infer.NET pour une régression bayésienne. Ce track présuppose .NET 9.0 + dotnet-interactive.

### Track B : Data Science with Agents (Python, 22 notebooks, ~20h)

Le parcours Python commence par les fondations (NumPy/Pandas) puis se divise en deux sous-tracks. Le sous-track **LangChain** (Labs 1-7) couvre le data wrangling, la visualisation, le ML classique (régression, classification, clustering), les modèles d'ensemble et le NLP de base. Le sous-track **Google ADK** (Labs 8-17) monte en complexité avec le deep learning (PyTorch), l'analyse de survivors, le dashboarding, et les pipelines agentic (agents LLM pour automatiser le workflow data science). Ce track présuppose Python 3.10+ avec PyTorch, scikit-learn et pandas.

## Positionnement pedagogique

Cette série sert les cours **ECE / EPITA / EPF** en introduction au Machine Learning appliqué. Elle se situe après les fondamentaux de programmation (Python ou C#) et avant les séries spécialisées ([QuantConnect](../QuantConnect/) pour le trading, [RL](../RL/) pour l'apprentissage par renforcement). Aucune prérequis en statistiques avancées : les concepts sont introduits au fil des notebooks.

**Slides de cours associes** : [06-apprentissage/](../../slides/06-apprentissage/) | **Livre de reference** : [Hands-On AI Trading](https://www.hands-on-ai-trading.com/) (chapitres ML)

**30 notebooks** | **2 sous-domaines** | **~25h** | **.NET Interactive + Python**

## Structure

```
ML/
├── ML.Net/                           # Tutoriels ML.NET (C#)
│   ├── ML-1-Introduction.ipynb
│   ├── ML-2-Data&Features.ipynb
│   ├── ML-3-Entrainement&AutoML.ipynb
│   ├── ML-4-Evaluation.ipynb
│   ├── ML-5-TimeSeries.ipynb
│   ├── ML-6-ONNX.ipynb
│   ├── ML-7-Recommendation.ipynb
│   ├── TP-prevision-ventes.ipynb
│   └── taxi-fare.csv
│
└── DataScienceWithAgents/            # Data Science Python + AI Agents
    ├── 01-PythonForDataScience/      # Fondations NumPy/Pandas
    ├── PythonAgentsForDataScience/   # Track LangChain (Labs 1-7)
    └── AgenticDataScience/           # Track Google ADK (Labs 8-17)
```

## ML.NET (C# / .NET Interactive)

Serie de 8 notebooks couvrant ML.NET de l'introduction a l'evaluation avancee. Vous apprendrez a construire un pipeline ML complet en C#, du chargement de donnees au deploiement ONNX, en passant par l'entrainement, l'AutoML, et l'evaluation rigoureuse.

| # | Notebook | Contenu | Focus |
|---|----------|---------|-------|
| 1 | [ML-1-Introduction](ML.Net/ML-1-Introduction.ipynb) | Hello ML.NET World, pipeline de base | Fondamentaux |
| 2 | [ML-2-Data&Features](ML.Net/ML-2-Data&Features.ipynb) | IDataView, TextLoader, encodage | Preparation donnees |
| 3 | [ML-3-Entrainement&AutoML](ML.Net/ML-3-Entrainement&AutoML.ipynb) | SDCA, LightGBM, AutoML | Entrainement |
| 4 | [ML-4-Evaluation](ML.Net/ML-4-Evaluation.ipynb) | Cross-validation, metriques, PFI | Evaluation |
| 5 | [ML-5-TimeSeries](ML.Net/ML-5-TimeSeries.ipynb) | Forecasts temporelles, windowing | Series temporelles |
| 6 | [ML-6-ONNX](ML.Net/ML-6-ONNX.ipynb) | Export ONNX, inference en production | Deployement |
| 7 | [ML-7-Recommendation](ML.Net/ML-7-Recommendation.ipynb) | Système de recommandation | Recommandations |
| 8 | [TP-prevision-ventes](ML.Net/TP-prevision-ventes.ipynb) | Regression bayesienne (Infer.NET) | Application pratique |

### Installation ML.NET

```bash
# 1. Installer .NET SDK 9.0+ depuis https://dotnet.microsoft.com/download
dotnet tool install -g Microsoft.dotnet-interactive
dotnet interactive jupyter install

# Verification
jupyter kernelspec list  # doit montrer .net-csharp
```

Documentation complete : [ML.Net/README.md](ML.Net/README.md)

## Python Data Science with Agents

Formation complete en Data Science Python enrichie d'agents IA. Vous commencerez par les fondamentaux (NumPy, Pandas), puis construirez des agents LLM capables d'analyser des donnees, de nettoyer des datasets, et de participer a des competitions Kaggle. La seconde moitie plonge dans les frameworks Google ADK pour construire des systemes multi-agents avances.

### Fondations (01-PythonForDataScience)

| Notebook | Contenu |
|----------|---------|
| [1.2-NumPy](DataScienceWithAgents/01-PythonForDataScience/notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb) | Arrays, vectorisation, operations |
| [1.3-Pandas](DataScienceWithAgents/01-PythonForDataScience/notebooks/1.3-Analyse_de_Donnees_avec_Pandas.ipynb) | DataFrames, filtrage, manipulation |

### Workshop 3 Jours (PythonAgentsForDataScience)

| Jour | Lab | Nom | Objectif |
|------|-----|-----|----------|
| **Day 1** | 1 | Python for Data Science | Revision Pandas, Matplotlib, Scikit-Learn |
| **Day 2** | 2 | RFP Analysis | Parser des appels d'offres avec agents LLM |
| **Day 2** | 3 | CV Screening | Scoring CV avec agents IA |
| **Day 3** | 4 | Data Wrangling | Nettoyage et transformation de donnees |
| **Day 3** | 5 | Viz & ML | Visualisation et intro Scikit-Learn |
| **Day 3** | 6 | First Agent | Construire un agent simple (LLM + Tools) |
| **Day 3** | 7 | Data Analysis Agent | Agent pour interroger des DataFrames |

### Track AgenticDataScience (Days 4-7)

Track avance integrant les frameworks Google ADK (DS-STAR, MLE-STAR) avec support multi-provider (Gemini 3.1, vLLM, OpenAI).

| Jour | Lab | Nom | Objectif |
|------|-----|-----|----------|
| **Day 4** | 8 | ADK Introduction | Architecture ADK, configuration providers |
| **Day 4** | 9 | First ADK Agent | Premier agent pour Data Science |
| **Day 5** | 10 | File Analyzer | Analyse de fichiers heterogenes |
| **Day 5** | 11 | Planner-Coder Loop | Boucle iterative multi-agents |
| **Day 5** | 12 | DS-Star Workshop | Application complete DS-STAR |
| **Day 6** | 13 | Web Search SOTA | Recherche de modeles SOTA |
| **Day 6** | 14 | Ablation Refinement | Optimisation ciblee par ablation |
| **Day 6** | 15 | Kaggle Challenge | Competition Kaggle avec MLE-STAR |
| **Day 7** | 16 | Data Science Agent | Agent BigQuery/BQML |
| **Day 7** | 17 | Final Project | Projet integre |

Documentation complete : [DataScienceWithAgents/AgenticDataScience/README.md](DataScienceWithAgents/AgenticDataScience/README.md)

### Installation Python DataScience Labs (Days 1-3)

```bash
pip install pandas numpy matplotlib seaborn scikit-learn ipywidgets
# Labs 2-3 et 6-7 necessitent aussi :
pip install langchain langchain-openai langchain-experimental
# + variable d'environnement OPENAI_API_KEY dans un fichier .env
```

### Installation AgenticDataScience Labs (Days 4-7)

```bash
pip install -r MyIA.AI.Notebooks/ML/DataScienceWithAgents/AgenticDataScience/requirements.txt
cp .env.example .env  # puis configurer les cles API
```

Providers LLM supportes (Labs 8+) : Google Gemini (recommande), OpenAI, OpenRouter, vLLM local, LM Studio.

Documentation complete : [DataScienceWithAgents/README.md](DataScienceWithAgents/README.md)

## Public cible

| Section | Audience | Prerequis |
|---------|----------|-----------|
| **ML.NET** | Developpeurs C#/.NET, environnements enterprise | C# base, .NET SDK 9.0+ |
| **Python Data Science (Days 1-3)** | Analystes, data scientists, debutants-intermediaires | Python base, Jupyter |
| **AI Agents (Days 4-7)** | Praticiens IA souhaitant integrer LLMs | Days 1-3 ou experience equivalente |

## Progression recommandee

### Parcours Data Scientist classique (~12h)

1. [ML-1](ML.Net/ML-1-Introduction.ipynb) → comprendre le pipeline ML
1. [NumPy](DataScienceWithAgents/01-PythonForDataScience/notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb) + [Pandas](DataScienceWithAgents/01-PythonForDataScience/notebooks/1.3-Analyse_de_Donnees_avec_Pandas.ipynb) → maitriser les donnees
1. [ML-2](ML.Net/ML-2-Data&Features.ipynb) + [ML-3](ML.Net/ML-3-Entrainement&AutoML.ipynb) → entrainer des modeles
1. [ML-4](ML.Net/ML-4-Evaluation.ipynb) → evaluer rigoureusement

### Parcours AI Agent Builder (~15h)

1. Days 1-3 (Labs 1-7) : Data Science + LangChain
1. Days 4-7 (Labs 8-17) : Google ADK + multi-agents
1. Projets finaux : Kaggle + BigQuery

### Parcours Enterprise .NET (~6h)

1. [ML-1](ML.Net/ML-1-Introduction.ipynb) a [ML-4](ML.Net/ML-4-Evaluation.ipynb) : fondamentaux ML.NET
1. [ML-5](ML.Net/ML-5-TimeSeries.ipynb) : series temporelles
1. [ML-6](ML.Net/ML-6-ONNX.ipynb) : interop Python → .NET
1. [TP-prevision-ventes](ML.Net/TP-prevision-ventes.ipynb) : projet integre

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Pipeline ML** | Enchainement data loading → features → training → evaluation |
| **Feature Engineering** | One-hot encoding, normalisation, concatenation |
| **AutoML** | Recherche automatique d'hyperparametres |
| **Evaluation** | R², MAE, RMSE, cross-validation |
| **Agents IA** | LLM + Tools + Prompt + Executor |

## Ressources

### ML.NET

- [Documentation ML.NET](https://docs.microsoft.com/en-us/dotnet/machine-learning/)
- [ML.NET Samples](https://github.com/dotnet/machinelearning-samples)
- [Hands-On AI Trading](https://www.hands-on-ai-trading.com/) — chapitres ML.NET et pipeline de trading

### Python Data Science

- [Pandas Documentation](https://pandas.pydata.org/docs/)
- [Scikit-Learn User Guide](https://scikit-learn.org/stable/user_guide.html)
- [LangChain Documentation](https://python.langchain.com/)
- [Google ADK Documentation](https://google.github.io/adk-docs/)

## Licence

Voir la licence du repository principal.

---

## Cross-series Bridges

| Serie | Lien | Connection |
|-------|------|-------------|
| [RL](../RL/README.md) | Apprentissage par renforcement | Le RL s'appuie sur les memes fondamentaux ML (gradients, reseaux de neurones, evaluation) |
| [GenAI](../GenAI/README.md) | IA generative | Les agents IA du track DataScienceWithAgents utilisent les LLMs couverts dans GenAI/Texte |
| [QuantConnect](../QuantConnect/README.md) | Trading algorithmique | Les modeles de prediction ML (regression, classification) s'appliquent directement aux strategies de trading |
| [Probas](../Probas/README.md) | Programmation probabiliste | L'evaluation bayesienne des modeles (TP-prevision-ventes) est une application directe de la serie Probas |
| [Search](../Search/README.md) | Recherche et optimisation | L'optimisation des hyperparametres ML rejoint les techniques de recherche (grille, bayesienne) |

---

## Navigation

- [<- Notebooks racine](../) | [GenAI ->](../GenAI/)
- [ML.NET ->](ML.Net/README.md) | [DataScienceWithAgents ->](DataScienceWithAgents/README.md) | [RL ->](../RL/)

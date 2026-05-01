# ML - Machine Learning

<!-- CATALOG-STATUS
series: ML
pedagogical_count: 30
breakdown: DataScienceWithAgents=22, ML.Net=8
updated: 2026-05-01
-->

Serie de notebooks couvrant le Machine Learning avec deux approches complementaires : **ML.NET** pour l'ecosysteme .NET/C# et **Python Data Science with Agents** pour les pipelines modernes avec LLMs.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 30 (8 C#, 22 Python) |
| Sous-dossiers | 2 (ML.Net, DataScienceWithAgents) |
| Duree totale estimee | ~25h |

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

Serie de 5 notebooks couvrant ML.NET de l'introduction a l'evaluation avancee.

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

Formation complete en Data Science Python avec integration d'agents IA.

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

| Section | Audience |
|---------|----------|
| **ML.NET** | Developpeurs C#/.NET, environnements enterprise |
| **Python Data Science** | Analystes, data scientists, debutants-intermediaires |
| **AI Agents** | Praticiens IA souhaitant integrer LLMs |

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

### Python Data Science

- [Pandas Documentation](https://pandas.pydata.org/docs/)
- [Scikit-Learn User Guide](https://scikit-learn.org/stable/user_guide.html)
- [LangChain Documentation](https://python.langchain.com/)

## Licence

Voir la licence du repository principal.

---

## Voir aussi

**[Reinforcement Learning](../RL/)** - Series dediee a l'apprentissage par renforcement avec Stable Baselines3 (PPO, DQN, experience replay). 3 notebooks complementaires pour approfondir les techniques de RL.

# ML - Machine Learning

Serie de notebooks couvrant le Machine Learning avec deux approches complementaires : **ML.NET** pour l'ecosysteme .NET/C# et **Python Data Science with Agents** pour les pipelines modernes avec LLMs.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 14 (5 C#, 9 Python) |
| Sous-dossiers | 2 (ML.Net, DataScienceWithAgents) |
| Duree totale estimee | ~8-10h |

## Structure

```
ML/
├── ML.Net/                           # Tutoriels ML.NET (C#)
│   ├── ML-1-Introduction.ipynb
│   ├── ML-2-Data&Features.ipynb
│   ├── ML-3-Entrainement&AutoML.ipynb
│   ├── ML-4-Evaluation.ipynb
│   ├── TP-prevision-ventes.ipynb
│   └── taxi-fare.csv
│
└── DataScienceWithAgents/            # Data Science Python + AI Agents
    ├── 01-PythonForDataScience/      # Fondations NumPy/Pandas
    └── PythonAgentsForDataScience/   # Workshop 3 jours (Labs 1-7)
```

## ML.NET (C# / .NET Interactive)

Serie de 5 notebooks couvrant ML.NET de l'introduction a l'evaluation avancee.

| # | Notebook | Contenu | Focus |
|---|----------|---------|-------|
| 1 | [ML-1-Introduction](ML.Net/ML-1-Introduction.ipynb) | Hello ML.NET World, pipeline de base | Fondamentaux |
| 2 | [ML-2-Data&Features](ML.Net/ML-2-Data&Features.ipynb) | IDataView, TextLoader, encodage | Preparation donnees |
| 3 | [ML-3-Entrainement&AutoML](ML.Net/ML-3-Entrainement&AutoML.ipynb) | SDCA, LightGBM, AutoML | Entrainement |
| 4 | [ML-4-Evaluation](ML.Net/ML-4-Evaluation.ipynb) | Cross-validation, metriques, PFI | Evaluation |
| 5 | [TP-prevision-ventes](ML.Net/TP-prevision-ventes.ipynb) | Regression bayesienne (Infer.NET) | Application pratique |

### Prerequis ML.NET

```bash
# .NET SDK 9.0 requis
dotnet --version

# Packages NuGet (installes dans les notebooks)
# - Microsoft.ML
# - Microsoft.ML.AutoML
# - Microsoft.Data.Analysis
# - Microsoft.ML.Probabilistic
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

### Prerequis Python

```bash
# Environnement Python
python -m venv venv
venv\Scripts\activate  # Windows

# Dependances
pip install numpy pandas scikit-learn matplotlib seaborn
pip install langchain openai python-dotenv  # Pour agents
```

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

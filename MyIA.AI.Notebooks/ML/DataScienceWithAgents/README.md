# DataScienceWithAgents - Data Science Python avec Agents IA

Formation complete en Data Science Python avec integration d'agents IA. Combine les fondamentaux NumPy/Pandas avec deux tracks complementaires : LangChain (3 jours) et Google ADK (4 jours).

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 19 (7 LangChain + 10 ADK + 2 fondations) |
| Kernel | Python 3.11+ |
| Duree totale | ~7 jours |

## Structure

```
DataScienceWithAgents/
├── 01-PythonForDataScience/    # Fondations (2 notebooks)
│   └── notebooks/
│       ├── 1.2-NumPy.ipynb
│       └── 1.3-Pandas.ipynb
│
├── PythonAgentsForDataScience/ # Track LangChain (7 labs)
│   ├── Day1/Labs/              # Revision
│   ├── Day2/Labs/              # Agents RFP et CV
│   └── Day3/Labs/              # Data + Agents
│
└── AgenticDataScience/         # Track Google ADK (10 labs)
    ├── Day4-Foundations/       # Introduction ADK
    ├── Day5-DS-Star/           # Data Science autonome
    ├── Day6-MLE-Star/          # ML Engineering
    └── Day7-Production/        # Integration GCP
```

## Fondations (01-PythonForDataScience)

| Notebook | Contenu | Duree |
|----------|---------|-------|
| [1.2-NumPy](01-PythonForDataScience/notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb) | Arrays, operations, vectorisation | 45 min |
| [1.3-Pandas](01-PythonForDataScience/notebooks/1.3-Analyse_de_Donnees_avec_Pandas.ipynb) | DataFrames, filtrage, groupby | 60 min |

## Workshop 3 Jours (PythonAgentsForDataScience)

### Day 1 - Revision Python

| Lab | Notebook | Contenu |
|-----|----------|---------|
| 1 | [Lab1-PythonForDataScience](PythonAgentsForDataScience/Day1/Labs/Lab1-PythonForDataScience.ipynb) | Pandas, Matplotlib, Scikit-Learn |

### Day 2 - Agents Documentaires

| Lab | Notebook | Contenu |
|-----|----------|---------|
| 2 | [Lab2-RFP-Analysis](PythonAgentsForDataScience/Day2/Labs/Lab2-RFP-Analysis/Lab2-RFP-Analysis.ipynb) | Parser des appels d'offres avec LLM |
| 3 | [Lab3-CV-Screening](PythonAgentsForDataScience/Day2/Labs/Lab3-CV-Screening/Lab3-CV-Screening.ipynb) | Scoring CV avec agents IA |

### Day 3 - Data + Agents

| Lab | Notebook | Contenu |
|-----|----------|---------|
| 4 | [Lab4-DataWrangling](PythonAgentsForDataScience/Day3/Labs/Lab4-DataWrangling/Lab4-DataWrangling.ipynb) | Nettoyage et transformation |
| 5 | [Lab5-Viz-ML](PythonAgentsForDataScience/Day3/Labs/Lab5-Viz-ML/Lab5-Viz-ML.ipynb) | Visualisation et intro ML |
| 6 | [Lab6-First-Agent](PythonAgentsForDataScience/Day3/Labs/Lab6-First-Agent/Lab6-First-Agent.ipynb) | Construction d'un agent simple |
| 7 | [Lab7-Data-Analysis-Agent](PythonAgentsForDataScience/Day3/Labs/Lab7-Data-Analysis-Agent/Lab7-Data-Analysis-Agent.ipynb) | Agent pour DataFrames |

## Technologies

| Categorie | Technologies |
|-----------|--------------|
| **Data Science** | NumPy, Pandas, Matplotlib, Seaborn |
| **Machine Learning** | Scikit-Learn |
| **Agents IA** | LangChain, OpenAI GPT |
| **Orchestration** | python-dotenv |

## Installation

```bash
# Environnement Python
python -m venv venv
venv\Scripts\activate  # Windows
source venv/bin/activate  # Linux/Mac

# Labs 1 et 4-5 (Data Science de base)
pip install pandas numpy matplotlib seaborn scikit-learn ipywidgets

# Labs 2-3 et 6-7 (Agents LangChain)
pip install langchain langchain-openai langchain-experimental python-dotenv
```

### Configuration API (Labs 2-3, 6-7)

```bash
# Creer un fichier .env a la racine du projet
OPENAI_API_KEY=sk-...
```

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Agent** | LLM + Outils + Prompt + Executeur |
| **Tool** | Fonction appelable par l'agent |
| **Chain** | Sequence d'operations LLM |
| **Memory** | Contexte conversationnel |

## Public cible

- Analystes de donnees souhaitant integrer l'IA
- Data scientists interessés par les agents
- Developpeurs Python intermediaires

## Parcours recommande

```
01-PythonForDataScience (prereq)
    |
Day 1: Lab 1 (revision)
    |
Day 2: Labs 2-3 (agents documentaires)
    |
Day 3: Labs 4-7 (data + agents)
```

## Ressources

- [Pandas Documentation](https://pandas.pydata.org/docs/)
- [LangChain Documentation](https://python.langchain.com/)
- [OpenAI Cookbook](https://cookbook.openai.com/)

## Track AgenticDataScience (Days 4-7)

Track avance integrant les frameworks Google ADK (DS-STAR, MLE-STAR) avec support multi-provider.

### Day 4 - ADK Foundations (Labs 8-9)

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 8 | [ADK-Introduction](AgenticDataScience/Day4-Foundations/Lab8-ADK-Introduction.ipynb) | Architecture ADK, configuration providers |
| 9 | [First-ADK-Agent](AgenticDataScience/Day4-Foundations/Lab9-First-ADK-Agent.ipynb) | Premier agent pour Data Science |

### Day 5 - DS-STAR (Labs 10-12)

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 10 | [File-Analyzer](AgenticDataScience/Day5-DS-Star/Lab10-File-Analyzer.ipynb) | Analyse de fichiers heterogenes |
| 11 | [Planner-Coder-Loop](AgenticDataScience/Day5-DS-Star/Lab11-Planner-Coder-Loop.ipynb) | Boucle iterative multi-agents |
| 12 | [DS-Star-Workshop](AgenticDataScience/Day5-DS-Star/Lab12-DS-Star-Workshop.ipynb) | Application complete |

### Day 6 - MLE-STAR (Labs 13-15)

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 13 | [Web-Search-SOTA](AgenticDataScience/Day6-MLE-Star/Lab13-Web-Search-SOTA.ipynb) | Recherche de modeles SOTA |
| 14 | [Ablation-Refinement](AgenticDataScience/Day6-MLE-Star/Lab14-Ablation-Refinement.ipynb) | Optimisation ciblee |
| 15 | [Kaggle-Challenge](AgenticDataScience/Day6-MLE-Star/Lab15-Kaggle-Challenge.ipynb) | Competition Kaggle |

### Day 7 - Production (Labs 16-17)

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 16 | [Data-Science-Agent](AgenticDataScience/Day7-Production/Lab16-Data-Science-Agent.ipynb) | Agent BigQuery/BQML |
| 17 | [Final-Project](AgenticDataScience/Day7-Production/Lab17-Final-Project.ipynb) | Projet integre |

### Technologies AgenticDataScience

| Categorie | Technologies |
|-----------|--------------|
| **Abstraction** | LiteLLM (multi-provider) |
| **Google ADK** | google-adk, google-generativeai |
| **Providers** | Gemini 3.1, vLLM, OpenAI, OpenRouter |
| **Cloud (Day 7)** | BigQuery, Vertex AI, BQML |

Documentation complete : [AgenticDataScience/README.md](AgenticDataScience/README.md)

## Licence

Voir la licence du repository principal.

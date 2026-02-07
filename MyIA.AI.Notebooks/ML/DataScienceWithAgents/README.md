# DataScienceWithAgents - Data Science Python avec Agents IA

Formation complete en Data Science Python avec integration d'agents IA. Combine les fondamentaux NumPy/Pandas avec un workshop de 3 jours sur les agents LLM.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 9 |
| Kernel | Python 3 |
| Duree totale | ~3 jours (workshop) |

## Structure

```
DataScienceWithAgents/
├── 01-PythonForDataScience/    # Fondations (2 notebooks)
│   └── notebooks/
│       ├── 1.2-NumPy.ipynb
│       └── 1.3-Pandas.ipynb
│
└── PythonAgentsForDataScience/ # Workshop 3 jours (7 labs)
    ├── Day1/Labs/              # Revision
    ├── Day2/Labs/              # Agents RFP et CV
    └── Day3/Labs/              # Data + Agents
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

## Prerequisites

```bash
# Environnement Python
python -m venv venv
venv\Scripts\activate  # Windows

# Dependances Data Science
pip install numpy pandas matplotlib seaborn scikit-learn

# Dependances Agents (Day 2-3)
pip install langchain openai python-dotenv
```

### Configuration API

```bash
# Dans .env
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

## Licence

Voir la licence du repository principal.

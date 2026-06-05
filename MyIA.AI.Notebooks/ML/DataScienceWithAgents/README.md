# DataScienceWithAgents - Data Science Python avec Agents IA

Formation complete en Data Science Python avec integration d'agents IA. Combine les fondamentaux NumPy/Pandas avec deux tracks complementaires : LangChain (3 jours) et Google ADK (4 jours).

Au-dela des bibliotheques classiques, cette formation explore un changement de paradigme : passer de *l'ecriture* de code data science a *l'orchestration* d'**agents LLM** qui le produisent et l'executent. Apres les fondations NumPy/Pandas, le track **LangChain** apprend a construire des agents capables d'interroger un DataFrame, de nettoyer un jeu de donnees ou de scorer des candidatures ; le track **Google ADK** monte en puissance avec des systemes multi-agents (boucles planner-coder, frameworks DS-STAR / MLE-STAR) jusqu'a concourir sur des competitions Kaggle. L'enjeu pedagogique n'est pas seulement technique : il s'agit de comprendre *quand* un agent autonome accelere reellement le travail d'analyse, et *comment* l'encadrer (outils, validation, garde-fous).

## Pourquoi cette serie

Le Data Science traditionnel suit un workflow manuel : charger, nettoyer, transformer, modeliser, evaluer. Cette serie introduit un **changement de paradigme** : orchestrer des agents LLM qui automatisent ce workflow. L'objectif n'est pas de remplacer le data scientist, mais de comprendre *quand* un agent accelere reellement le travail et *comment* l'encadrer.

La formation couvre deux stacks complementaires :

| Aspect | Track LangChain (Days 1-3) | Track Google ADK (Days 4-7) |
|--------|---------------------------|----------------------------|
| **Approche** | Agent unique avec tools | Systemes multi-agents |
| **Framework** | LangChain + OpenAI | Google ADK + LiteLLM |
| **Complexite** | Chains, outils simples | Boucles planner-coder, DS-STAR |
| **Application** | RFP, CV screening, data wrangling | Kaggle, BigQuery, deploiement |
| **Providers** | OpenAI uniquement | Multi-provider (Gemini, vLLM, OpenAI) |

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

## Objectifs d'apprentissage

A l'issue de cette serie, vous serez capable de :

1. **Construire** un agent LLM avec LangChain (tools, chains, memory) et l'appliquer a des taches data science concretes
2. **Evaluer** quand un agent autonome accelere le travail d'analyse vs une approche manuelle
3. **Orchestrer** des systemes multi-agents avec Google ADK (planner-coder, DS-STAR, MLE-STAR)
4. **Configurer** un pipeline multi-provider (Gemini, OpenAI, vLLM local) via LiteLLM
5. **Deployer** un agent data science en production (BigQuery, BQML, GCP)

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Agent** | LLM + Outils + Prompt + Executeur |
| **Tool** | Fonction appelable par l'agent |
| **Chain** | Sequence d'operations LLM |
| **Memory** | Contexte conversationnel |

## Public cible

- Analystes de donnees souhaitant integrer l'IA
- Data scientists interesses par les agents
- Developpeurs Python intermediaires

## Quel parcours choisir

### Parcours analyste data science (~3 jours)

Labs 1-7 en sequence. Acquerir les bases Pandas, puis construire des agents LangChain pour automatiser l'analyse de donnees.

1. Lab 1 -> revision Pandas/Matplotlib/Scikit-Learn
2. Labs 2-3 -> agents documentaires (RFP, CV)
3. Labs 4-7 -> data wrangling + agents d'analyse

### Parcours ingenieur ML agentique (~4 jours)

Labs 8-17 en sequence. Monter en complexite avec les frameworks Google ADK et les systemes multi-agents.

1. Labs 8-9 -> architecture ADK, premier agent
2. Labs 10-12 -> DS-STAR (data science autonome)
3. Labs 13-15 -> MLE-STAR (Kaggle, optimisation)
4. Labs 16-17 -> production (BigQuery, projet final)

### Parcours complet (~7 jours)

Tous les labs en sequence, des fondations NumPy/Pandas jusqu'au deploiement GCP.

### Parcours rapide (~1 jour)

Labs 1 + 6 + 8. Decouvrir le pipeline data science, construire un premier agent LangChain, puis un premier agent ADK. Les trois labs les plus representatifs pour une premiere prise en main.

## FAQ / Troubleshooting

### `langchain` ou `langchain-openai` echoue a l'import

Verifier que le bon environnement est active :

```bash
# verifier l'environnement
which python  # Linux/Mac
where python  # Windows
# doit pointer vers votre venv, pas le systeme

# re-installer si necessaire
pip install langchain langchain-openai langchain-experimental
```

Si l'erreur persiste, verifier la version Python (3.10+ requis) : `python --version`.

### Erreur "OPENAI_API_KEY not found" dans les Labs 2-3 et 6-7

Ces labs necessitent une cle API OpenAI. Creer un fichier `.env` a la racine du projet :

```bash
# A la racine du repo ou a cote des notebooks
echo 'OPENAI_API_KEY=sk-...' > .env
```

Le package `python-dotenv` charge automatiquement ce fichier. Ne JAMAIS committer le fichier `.env` (il est dans `.gitignore`).

### Les agents ADK ne se connectent pas au provider (Labs 8+)

Verifier la configuration dans le fichier `.env` d'AgenticDataScience :

```bash
# Provider recommande (cle gratuite)
ACTIVE_PROVIDER=gemini
GEMINI_API_KEY=AIza...

# Ou provider local (pas de cle requise)
ACTIVE_PROVIDER=vllm
VLLM_BASE_URL=http://localhost:8000/v1
```

Si vous utilisez Gemini, obtenir une cle gratuite sur [aistudio.google.com](https://aistudio.google.com).

### `ModuleNotFoundError` pour un package dans un lab

Chaque lab a des dependances specifiques. Installer les packages au fur et a mesure :

```bash
# Labs 1, 4-5 (data science classique)
pip install pandas numpy matplotlib seaborn scikit-learn ipywidgets

# Labs 2-3, 6-7 (agents LangChain)
pip install langchain langchain-openai langchain-experimental python-dotenv

# Labs 8-17 (ADK)
pip install -r AgenticDataScience/requirements.txt
```

### Comment passer de LangChain a Google ADK ?

Les concepts se correspondent :

| Concept LangChain | Equivalent ADK |
|-------------------|----------------|
| `LLMChain` | ADK Agent avec instruction |
| `Tool` | ADK FunctionTool |
| `AgentExecutor` | ADK Runner |
| `ConversationBufferMemory` | ADK Session |
| `SequentialChain` | Boucle Planner-Coder |

Le passage se fait naturellement au Lab 8 qui reprend les memes concepts avec l'API ADK.

### Le kernel Jupyter n'affiche pas les outputs des agents

Certains agents produisent des outputs longs. Verifier :

1. La cellule n'est pas en timeout (augmenter le timeout du kernel)
2. Le provider repond (tester avec un appel simple : `client.chat.completions.create(...)`)
3. Les prints intermediaires sont flushes : `print(..., flush=True)`

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

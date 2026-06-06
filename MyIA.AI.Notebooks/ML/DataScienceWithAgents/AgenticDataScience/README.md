# AgenticDataScience - Agents IA pour Data Science avec Google ADK

Formation avancee sur les agents IA pour la Data Science, integrant les frameworks Google ADK (DS-STAR, MLE-STAR) avec support multi-provider.

## Pourquoi cette serie

Les frameworks d'agents IA (AutoGPT, CrewAI, ADK) promettent d'automatiser le travail du data scientist. Mais passer du demo au pipeline production-ready demande une comprehension approfondie des patterns d'orchestration. Cette serie vous apprend a construire des systemes multi-agents qui **fonctionnent reellement** sur des taches de data science complexes.

Les deux frameworks couverts (DS-STAR et MLE-STAR) representent l'etat de l'art en agents data science, publies par Google Research. Ils resolvent des problemes concrets :

| Framework | Probleme resolu | Pattern |
|-----------|----------------|---------|
| **DS-STAR** | Analyse de datasets heterogenes | Boucle Planner-Coder-Verifier |
| **MLE-STAR** | Competitions Kaggle automatisées | Recherche SOTA + Ablation + Refinement |

La particularite de cette serie : le support **multi-provider** (Gemini, vLLM, OpenAI, OpenRouter) via LiteLLM. Vous n'etes pas verrouille a un fournisseur LLM et pouvez tester avec un modele local gratuit.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 10 (Labs 8-17) |
| Kernel | Python 3.11+ |
| Durée totale | ~4 jours |
| Prérequis | Days 1-3 ou équivalent |

## Architecture Multi-Provider

Ce track utilise une **couche d'abstraction provider** permettant de brancher n'importe quel LLM compatible OpenAI :

```
┌─────────────────────────────────────────────────────────────┐
│                    AgenticDataScience                        │
├─────────────────────────────────────────────────────────────┤
│  Provider Abstraction Layer (LiteLLM)                        │
├──────────────┬──────────────┬──────────────┬────────────────┤
│   Gemini     │   OpenAI     │    vLLM      │   Autre        │
│   3.1 API    │  Compatible  │   Reverse    │   OpenAI API   │
└──────────────┴──────────────┴──────────────┴────────────────┘
```

### Providers Supportés

| Provider | Endpoint | Use Case |
|----------|----------|----------|
| **Google Gemini 3.1** | API Google | Production, meilleure performance |
| **vLLM via reverse proxy** | Votre endpoint | Modèles locaux hébergés |
| **OpenAI** | api.openai.com | Alternative cloud |
| **OpenRouter** | openrouter.ai | Accès multi-modèles |

## Structure

```
AgenticDataScience/
├── config/                    # Configuration multi-provider
│   ├── providers.py           # Abstraction layer
│   └── .env.example           # Template configuration
│
├── utils/                     # Utilitaires partagés
│   └── llm_client.py          # Client LLM unifié
│
├── Day4-Foundations/          # Introduction à l'agentique
│   ├── Lab8-ADK-Introduction.ipynb
│   └── Lab9-First-ADK-Agent.ipynb
│
├── Day5-DS-Star/              # DS-STAR (Data Science autonome)
│   ├── Lab10-File-Analyzer.ipynb
│   ├── Lab11-Planner-Coder-Loop.ipynb
│   └── Lab12-DS-Star-Workshop.ipynb
│
├── Day6-MLE-Star/             # MLE-STAR (ML Engineering)
│   ├── Lab13-Web-Search-SOTA.ipynb
│   ├── Lab14-Ablation-Refinement.ipynb
│   └── Lab15-Kaggle-Challenge.ipynb
│
└── Day7-Production/           # Intégration GCP
    ├── Lab16-Data-Science-Agent.ipynb
    └── Lab17-Final-Project.ipynb
```

## Progression Pédagogique

### Day 4 - Foundations (Labs 8-9)

Introduction au framework ADK et configuration multi-provider.

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 8 | [ADK-Introduction](Day4-Foundations/Lab8-ADK-Introduction.ipynb) | Architecture ADK, configuration providers |
| 9 | [First-ADK-Agent](Day4-Foundations/Lab9-First-ADK-Agent.ipynb) | Premier agent pour Data Science |

### Day 5 - DS-STAR (Labs 10-12)

Data Science autonome avec l'architecture Planner-Coder-Verifier.

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 10 | [File-Analyzer](Day5-DS-Star/Lab10-File-Analyzer.ipynb) | Analyse de fichiers hétérogènes |
| 11 | [Planner-Coder-Loop](Day5-DS-Star/Lab11-Planner-Coder-Loop.ipynb) | Boucle itérative multi-agents |
| 12 | [DS-Star-Workshop](Day5-DS-Star/Lab12-DS-Star-Workshop.ipynb) | Application complète |

### Day 6 - MLE-STAR (Labs 13-15)

ML Engineering automatisé style Kaggle.

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 13 | [Web-Search-SOTA](Day6-MLE-Star/Lab13-Web-Search-SOTA.ipynb) | Recherche de modèles SOTA |
| 14 | [Ablation-Refinement](Day6-MLE-Star/Lab14-Ablation-Refinement.ipynb) | Optimisation ciblée |
| 15 | [Kaggle-Challenge](Day6-MLE-Star/Lab15-Kaggle-Challenge.ipynb) | Compétition Kaggle |

### Day 7 - Production (Labs 16-17)

Intégration GCP et projet final.

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 16 | [Data-Science-Agent](Day7-Production/Lab16-Data-Science-Agent.ipynb) | Agent BigQuery/BQML |
| 17 | [Final-Project](Day7-Production/Lab17-Final-Project.ipynb) | Projet intégré |

## Installation

### Environnement

```bash
# Python 3.11+
python -m venv venv
venv\Scripts\activate  # Windows
source venv/bin/activate  # Linux/Mac

# Toutes les dependances (depuis la racine du repo)
pip install -r MyIA.AI.Notebooks/ML/DataScienceWithAgents/AgenticDataScience/requirements.txt
```

### Configuration

```bash
# Depuis le dossier AgenticDataScience/
cp .env.example .env  # Linux/Mac
copy .env.example .env  # Windows

# Puis editer .env et renseigner les cles API du provider choisi
```

### Providers LLM supportes (Labs 8+)

| Provider | Variable cle | Notes |
|----------|-------------|-------|
| **Google Gemini** (recommande) | `GEMINI_API_KEY` | Cle gratuite sur aistudio.google.com |
| **OpenAI** | `OPENAI_API_KEY` | Direct ou via OpenRouter |
| **OpenRouter** | `OPENROUTER_API_KEY` | Acces multi-modeles |
| **vLLM local** | `VLLM_BASE_URL` | Via reverse proxy, pas de cle requise |
| **LM Studio** | `LMSTUDIO_BASE_URL` | Local, http://localhost:1234/v1 |

Definir `ACTIVE_PROVIDER=gemini` (ou `vllm`, `openai`, `openrouter`, `lmstudio`) dans `.env`.

## Technologies

| Categorie | Technologies |
|-----------|--------------|
| **Abstraction** | LiteLLM |
| **Google ADK** | google-adk, google-generativeai |
| **Data Science** | Pandas, NumPy, Scikit-Learn |
| **ML Engineering** | MLflow, Optuna |
| **Cloud (Day 7)** | BigQuery, Vertex AI, BQML |

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Provider Abstraction** | Couche unifiant tous les LLM via LiteLLM |
| **ADK Agent** | Agent Google avec tools, sessions, mémoire |
| **DS-STAR** | Architecture Planner-Coder-Verifier pour Data Science |
| **MLE-STAR** | Agent ML Engineering avec recherche SOTA et ablation |
| **Multi-provider** | Switch entre Gemini, vLLM, OpenAI sans changer le code |

## Objectifs d'apprentissage

A l'issue de cette serie, vous serez capable de :

1. **Configurer** un environnement multi-provider (Gemini, vLLM, OpenAI) via LiteLLM et l'abstraction ADK
2. **Construire** un agent ADK avec des outils personnalises (file analysis, web search, code execution)
3. **Orchestrer** une boucle Planner-Coder-Verifier pour l'analyse autonome de datasets (DS-STAR)
4. **Optimiser** un pipeline ML via recherche SOTA et ablation systematique (MLE-STAR)
5. **Deployer** un agent data science en production avec BigQuery et Vertex AI

## Public cible

- Data Scientists maitrisant Python
- Ingenieurs ML interesses par les agents
- Etudiants ayant complete Days 1-3 (LangChain)

## Prerequis

### Technique

- Python 3.11+ et environnements virtuels
- Connaissances Pandas/NumPy (niveau intermediaire)
- Notions de Machine Learning

### API/Cloud

| Mode | Prerequis | Labs Accessibles |
|------|-----------|------------------|
| **Local seul** | vLLM via reverse proxy | Days 4-6 |
| **Gemini API** | Cle API gratuite | Days 4-6 |
| **GCP complet** | Projet + Vertex AI | Days 4-7 |

## Quel parcours choisir

### Parcours agent data science (~2 jours)

Labs 8-12 en sequence. Maitriser DS-STAR pour automatiser l'analyse de datasets.

1. Labs 8-9 -> architecture ADK, premier agent avec outils
2. Labs 10-12 -> DS-STAR (file analyzer, planner-coder, workshop)

### Parcours ML engineering (~2 jours)

Labs 13-17 en sequence. MLE-STAR pour les competitions et le deploiement.

1. Labs 13-15 -> recherche SOTA, ablation, Kaggle
2. Labs 16-17 -> BigQuery/BQML, projet final

### Parcours complet (~4 jours)

Tous les labs (8-17) en sequence. Le parcours recommande pour une formation complete.

### Parcours rapide (~0.5 jour)

Labs 8 + 11 + 15. Architecture ADK, boucle planner-coder, et Kaggle. Les trois labs les plus representatifs.

## FAQ / Troubleshooting

### Le provider Gemini renvoie une erreur 429 (rate limit)

Gemini API free tier a un quota limité. Solutions :

```bash
# Option 1 : ajouter un delai entre les appels
# Dans votre code : time.sleep(2) entre les appels API

# Option 2 : basculer vers un autre provider
ACTIVE_PROVIDER=openai  # ou openrouter

# Option 3 : utiliser vLLM local (pas de rate limit)
ACTIVE_PROVIDER=vllm
VLLM_BASE_URL=http://localhost:8000/v1
```

### `ModuleNotFoundError: No module named 'google.adk'`

Le package google-adk n'est pas encore sur PyPI stable. Installer depuis le depot :

```bash
pip install -r AgenticDataScience/requirements.txt
# ou manuellement :
pip install google-generativeai litellm
```

### LiteLLM ne parvient pas a se connecter au provider

Verifier la configuration `.env` :

```bash
# Debug : afficher la config chargee
python -c "from litellm import completion; print('LiteLLM OK')"

# Verifier que le .env est bien charge
python -c "from dotenv import load_dotenv; import os; load_dotenv(); print(os.getenv('ACTIVE_PROVIDER'))"
```

Causes courantes : mauvais chemin `.env` (doit etre dans `AgenticDataScience/`), cle API invalide, ou URL base incorrecte pour vLLM.

### Les agents bouclent sans converger (Planner-Coder)

Le pattern Planner-Coder-Verifier peut entrer dans une boucle infinie si le prompt du verifier est trop laxiste. Ajuster :

1. Ajouter un **critere d'arret** explicite dans le prompt verifier (ex: "si le resultat est coherent avec les donnees, arreter")
2. Limiter le nombre d'iterations : `max_iterations = 5`
3. Verifier que le planner a acces aux **resultats** du coder (pas seulement au code)

### Comment passer de LangChain (Days 1-3) a ADK ?

Les concepts se correspondent directement :

| Concept LangChain | Equivalent ADK |
|-------------------|----------------|
| `ChatOpenAI` | `LiteLLM` + provider config |
| `Tool` decorator | `FunctionTool` |
| `AgentExecutor` | `Runner` + `Session` |
| `LLMChain` | Agent avec instruction |
| `ConversationMemory` | Session state |

Le Lab 8 (ADK Introduction) reprend les memes concepts avec la syntaxe ADK.

### Les Labs 16-17 (GCP) echouent sans projet Google Cloud

Les Labs 16-17 necessitent un projet GCP avec Vertex AI et BigQuery actives. Si vous n'avez pas acces GCP :

- Les Labs 8-15 sont **entirement autonomes** et ne necessitent que Gemini ou vLLM
- Le Lab 17 (Final Project) peut etre adapte avec un dataset local au lieu de BigQuery

## Ressources

- [Google ADK Documentation](https://github.com/google/adk-samples)
- [DS-STAR Paper](https://research.google/blog/ds-star-a-state-of-the-art-versatile-data-science-agent/)
- [MLE-STAR Paper](https://research.google/blog/mle-star-a-state-of-the-art-machine-learning-engineering-agents/)
- [LiteLLM Documentation](https://docs.litellm.ai/)

## Licence

Voir la licence du repository principal.

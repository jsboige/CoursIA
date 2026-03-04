# AgenticDataScience - Agents IA pour Data Science avec Google ADK

Formation avancée sur les agents IA pour la Data Science, intégrant les frameworks Google ADK (DS-STAR, MLE-STAR) avec support multi-provider.

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

# Dépendances
pip install -r requirements.txt
```

### Configuration

1. Copier `.env.example` vers `.env`
2. Configurer votre provider actif :

```bash
# Provider actif
ACTIVE_PROVIDER=gemini  # gemini, vllm, openai, openrouter

# === GEMINI 3.1 (Recommandé production) ===
GEMINI_API_KEY=your-gemini-key
GEMINI_MODEL=gemini-3.1-pro

# === vLLM via reverse proxy ===
VLLM_BASE_URL=https://your-vllm-endpoint.com/v1
VLLM_MODEL=qwen3.5-35b-a3b
VLLM_API_KEY=your-key-if-needed
```

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

## Public cible

- Data Scientists maitrisant Python
- Ingénieurs ML interessés par les agents
- Étudiants ayant complété Days 1-3 (LangChain)

## Prérequis

### Technique

- Python 3.11+ et environnements virtuels
- Connaissances Pandas/NumPy (niveau intermédiaire)
- Notions de Machine Learning

### API/Cloud

| Mode | Prérequis | Labs Accessibles |
|------|-----------|------------------|
| **Local seul** | vLLM via reverse proxy | Days 4-6 |
| **Gemini API** | Clé API gratuite | Days 4-6 |
| **GCP complet** | Projet + Vertex AI | Days 4-7 |

## Ressources

- [Google ADK Documentation](https://github.com/google/adk-samples)
- [DS-STAR Paper](https://research.google/blog/ds-star-a-state-of-the-art-versatile-data-science-agent/)
- [MLE-STAR Paper](https://research.google/blog/mle-star-a-state-of-the-art-machine-learning-engineering-agents/)
- [LiteLLM Documentation](https://docs.litellm.ai/)

## Licence

Voir la licence du repository principal.

# AgenticDataScience - Agents IA pour Data Science avec Google ADK

[← DataScienceWithAgents (parent)](../README.md) | [ML.NET (C#) →](../../ML.Net/README.md)

Formation avancée sur les agents IA pour la Data Science, intégrant les frameworks Google ADK (DS-STAR, MLE-STAR) avec support multi-provider.

## Pourquoi cette série

Les frameworks d'agents IA (AutoGPT, CrewAI, ADK) promettent d'automatiser le travail du data scientist. Mais passer du demo au pipeline production-ready demande une compréhension approfondie des patterns d'orchestration. Cette série vous apprend à construire des systèmes multi-agents qui **fonctionnent réellement** sur des tâches de data science complexes.

Les deux frameworks couverts (DS-STAR et MLE-STAR) représentent l'état de l'art en agents data science, publiés par Google Research. Ils résolvent des problèmes concrets :

| Framework | Problème résolu | Pattern |
|-----------|----------------|---------|
| **DS-STAR** | Analyse de datasets hétérogènes | Boucle Planner-Coder-Verifier |
| **MLE-STAR** | Compétitions Kaggle automatisées | Recherche SOTA + Ablation + Refinement |

La particularité de cette série : le support **multi-provider** (Gemini, vLLM, OpenAI, OpenRouter) via LiteLLM. Vous n'êtes pas verrouillé à un fournisseur LLM et pouvez tester avec un modèle local gratuit.

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

# Toutes les dépendances (depuis la racine du repo)
pip install -r MyIA.AI.Notebooks/ML/DataScienceWithAgents/AgenticDataScience/requirements.txt
```

### Configuration

```bash
# Depuis le dossier AgenticDataScience/
cp .env.example .env  # Linux/Mac
copy .env.example .env  # Windows

# Puis éditer .env et renseigner les clés API du provider choisi
```

### Providers LLM supportés (Labs 8+)

| Provider | Variable clé | Notes |
|----------|-------------|-------|
| **Google Gemini** (recommandé) | `GEMINI_API_KEY` | Clé gratuite sur aistudio.google.com |
| **OpenAI** | `OPENAI_API_KEY` | Direct ou via OpenRouter |
| **OpenRouter** | `OPENROUTER_API_KEY` | Accès multi-modèles |
| **vLLM local** | `VLLM_BASE_URL` | Via reverse proxy, pas de clé requise |
| **LM Studio** | `LMSTUDIO_BASE_URL` | Local, http://localhost:1234/v1 |

Définir `ACTIVE_PROVIDER=gemini` (ou `vllm`, `openai`, `openrouter`, `lmstudio`) dans `.env`.

## Technologies

| Catégorie | Technologies |
|-----------|--------------|
| **Abstraction** | LiteLLM |
| **Google ADK** | google-adk, google-generativeai |
| **Data Science** | Pandas, NumPy, Scikit-Learn |
| **ML Engineering** | MLflow, Optuna |
| **Cloud (Day 7)** | BigQuery, Vertex AI, BQML |

## Concepts clés

| Concept | Description |
|---------|-------------|
| **Provider Abstraction** | Couche unifiant tous les LLM via LiteLLM |
| **ADK Agent** | Agent Google avec tools, sessions, mémoire |
| **DS-STAR** | Architecture Planner-Coder-Verifier pour Data Science |
| **MLE-STAR** | Agent ML Engineering avec recherche SOTA et ablation |
| **Multi-provider** | Switch entre Gemini, vLLM, OpenAI sans changer le code |

## Objectifs d'apprentissage

À l'issue de cette série, vous serez capable de :

1. **Configurer** un environnement multi-provider (Gemini, vLLM, OpenAI) via LiteLLM et l'abstraction ADK
2. **Construire** un agent ADK avec des outils personnalisés (file analysis, web search, code execution)
3. **Orchestrer** une boucle Planner-Coder-Verifier pour l'analyse autonome de datasets (DS-STAR)
4. **Optimiser** un pipeline ML via recherche SOTA et ablation systématique (MLE-STAR)
5. **Déployer** un agent data science en production avec BigQuery et Vertex AI

## Public cible

- Data Scientists maîtrisant Python
- Ingénieurs ML intéressés par les agents
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

## Quel parcours choisir

### Parcours agent data science (~2 jours)

Labs 8-12 en séquence. Maîtriser DS-STAR pour automatiser l'analyse de datasets.

1. Labs 8-9 -> architecture ADK, premier agent avec outils
2. Labs 10-12 -> DS-STAR (file analyzer, planner-coder, workshop)

### Parcours ML engineering (~2 jours)

Labs 13-17 en séquence. MLE-STAR pour les compétitions et le déploiement.

1. Labs 13-15 -> recherche SOTA, ablation, Kaggle
2. Labs 16-17 -> BigQuery/BQML, projet final

### Parcours complet (~4 jours)

Tous les labs (8-17) en séquence. Le parcours recommandé pour une formation complète.

### Parcours rapide (~0.5 jour)

Labs 8 + 11 + 15. Architecture ADK, boucle planner-coder, et Kaggle. Les trois labs les plus représentatifs.

## FAQ / Troubleshooting

### Le provider Gemini renvoie une erreur 429 (rate limit)

Gemini API free tier a un quota limité. Solutions :

```bash
# Option 1 : ajouter un délai entre les appels
# Dans votre code : time.sleep(2) entre les appels API

# Option 2 : basculer vers un autre provider
ACTIVE_PROVIDER=openai  # ou openrouter

# Option 3 : utiliser vLLM local (pas de rate limit)
ACTIVE_PROVIDER=vllm
VLLM_BASE_URL=http://localhost:8000/v1
```

### `ModuleNotFoundError: No module named 'google.adk'`

Le package google-adk n'est pas encore sur PyPI stable. Installer depuis le dépôt :

```bash
pip install -r AgenticDataScience/requirements.txt
# ou manuellement :
pip install google-generativeai litellm
```

### LiteLLM ne parvient pas à se connecter au provider

Vérifier la configuration `.env` :

```bash
# Debug : afficher la config chargée
python -c "from litellm import completion; print('LiteLLM OK')"

# Vérifier que le .env est bien chargé
python -c "from dotenv import load_dotenv; import os; load_dotenv(); print(os.getenv('ACTIVE_PROVIDER'))"
```

Causes courantes : mauvais chemin `.env` (doit être dans `AgenticDataScience/`), clé API invalide, ou URL base incorrecte pour vLLM.

### Les agents bouclent sans converger (Planner-Coder)

Le pattern Planner-Coder-Verifier peut entrer dans une boucle infinie si le prompt du verifier est trop laxiste. Ajuster :

1. Ajouter un **critère d'arrêt** explicite dans le prompt verifier (ex: "si le résultat est cohérent avec les données, arrêter")
2. Limiter le nombre d'itérations : `max_iterations = 5`
3. Vérifier que le planner a accès aux **résultats** du coder (pas seulement au code)

### Comment passer de LangChain (Days 1-3) à ADK ?

Les concepts se correspondent directement :

| Concept LangChain | Équivalent ADK |
|-------------------|----------------|
| `ChatOpenAI` | `LiteLLM` + provider config |
| `Tool` decorator | `FunctionTool` |
| `AgentExecutor` | `Runner` + `Session` |
| `LLMChain` | Agent avec instruction |
| `ConversationMemory` | Session state |

Le Lab 8 (ADK Introduction) reprend les mêmes concepts avec la syntaxe ADK.

### Les Labs 16-17 (GCP) échouent sans projet Google Cloud

Les Labs 16-17 nécessitent un projet GCP avec Vertex AI et BigQuery activés. Si vous n'avez pas accès GCP :

- Les Labs 8-15 sont **entièrement autonomes** et ne nécessitent que Gemini ou vLLM
- Le Lab 17 (Final Project) peut être adapté avec un dataset local au lieu de BigQuery

## Conclusion

Vous avez parcouru l'intégralité du track agentique avancé : du premier agent ADK configurable à un pipeline de data science autonome déployable en production. L'enjeu n'était pas d'empiler des frameworks, mais de comprendre les **patterns d'orchestration** qui rendent un système multi-agents fiable au-delà de la démonstration.

### Ce que vous avez appris

- **Isoler le provider avant de choisir le modèle.** La couche LiteLLM a traité Gemini, vLLM, OpenAI et OpenRouter comme des backend interchangeables. La leçon durable : verrouiller une application sur un LLM unique est un risque architectural ; isoler le fournisseur derrière une interface est un investissement qui se rentabilise dès la première migration ou coupure de quota.
- **Le pattern Planner-Coder-Verifier (DS-STAR).** Un agent data science crédible n'est pas un prompt unique, mais une boucle où un *planner* décompose, un *coder* exécute, et un *verifier* confronte le résultat aux données avant d'itérer. La FAQ l'a montré concrètement : un verifier trop laxiste fait boucler le système, et c'est la rigueur du critère d'arrêt qui garantit la convergence.
- **La recherche SOTA comme point de départ (MLE-STAR).** Avant d'optimiser, l'agent identifie l'état de l'art puis mène une ablation systématique. C'est la transcription agentique du bon réflexe de praticien : on ne tune pas à l'aveugle, on part de la baseline publiée et on isole les variables une à une.
- **Du notebook au système déployé.** Les Labs 16-17 ont articulé l'agent avec BigQuery et Vertex AI, rappelant que la valeur d'un agent data science se mesure en production — coût, latence, volume de données — et non sur un notebook isolé.

### Prochaines étapes

- **Croiser l'agentique et le raisonnement formel** : la série [SymbolicAI](../../../SymbolicAI/) couple ces patterns d'orchestration avec des solveurs (CSP/SAT, planificateurs), et [GameTheory](../../../GameTheory/) introduit l'agent stratégique face à d'autres décideurs.
- **Approfondir l'hebergement de LLM** : les notebooks [GenAI](../../../GenAI/) détaillent l'auto-hebergement de modèles (Qwen, ComfyUI, vLLM) et le routage multi-modèle — la suite naturelle de votre couche LiteLLM quand vous voudrez quitter les APIs commerciales.
- **Décider sous incertitude** : la série [Probas/PyMC](../../../Probas/PyMC/) formalise la prise de décision bayésienne (théorie de l'utilité, valeur espérée de l'information) qu'un agent data science mature doit intégrer pour agir, pas seulement analyser.
- **Vous exercer en autonomie** : reprenez un problème Kaggle récent (Lab 15), traitez-le de bout en bout avec votre provider local, puis confrontez votre démarche à celle qu'a suivie l'agent MLE-STAR.

### Le fil rouge

La trame de cette série est la **réduction progressive de l'intervention humaine**. Les [Days 1-3 (PythonAgentsForDataScience)](../PythonAgentsForDataScience/) vous ont appris à *piloter* un agent ; DS-STAR lui a confié une analyse de bout en bout ; MLE-STAR lui a donné l'initiative de la recherche et de l'optimisation ; les Labs de production l'ont exposé à des contraintes réelles. La frontière entre « outil que l'on dirige » et « collègue que l'on encadre » est précisément ce que ces patterns d'orchestration déplacent — et c'est la compétence que cette série cherche à transmettre.

## Ressources

- [Google ADK Documentation](https://github.com/google/adk-samples)
- [DS-STAR Paper](https://research.google/blog/ds-star-a-state-of-the-art-versatile-data-science-agent/)
- [MLE-STAR Paper](https://research.google/blog/mle-star-a-state-of-the-art-machine-learning-engineering-agents/)
- [LiteLLM Documentation](https://docs.litellm.ai/)

## Licence

Voir la licence du repository principal.

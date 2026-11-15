# 07-Agent-Orchestration - Agents IA pour Data Science avec Google ADK

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
| Kernel | Python 3.11+ |
| Durée totale | ~4 jours |
| Prérequis | Days 1-3 ou équivalent |

Le catalogue du dépôt (`COURSE_CATALOG.generated.md`) est la source des décomptes — ce README présente les carnets, il ne les compte pas.

## Architecture Multi-Provider

Ce track utilise une **couche d'abstraction provider** permettant de brancher n'importe quel LLM compatible OpenAI :

```
┌─────────────────────────────────────────────────────────────┐
│                    07-Agent-Orchestration                        │
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
07-Agent-Orchestration/
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
│   ├── Lab12-DS-Star-Workshop.ipynb
│   ├── Lab12b-Sequential-Orchestration.ipynb
│   ├── Lab12c-Agent-Handoff.ipynb
│   ├── Lab12d-Token-Usage.ipynb
│   └── Lab12e-Session-Persistence.ipynb
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

## Comment lire ce README

La série propose un parcours principal par numéros nus et des approfondissements à ouvrir selon votre objectif ; [la racine du dépôt explique ce choix de vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous découvrez les agents de data science : suivez le parcours principal dans l'ordre.
- Vous creusez l'orchestration DS-STAR : ouvrez les approfondissements autour du Lab 12.
- Vous cherchez les sujets de recherche et les suites : consultez les parcours thématiques et les ressources.

## Parcours principal

### Day 4 - Foundations (Labs 8-9)

Introduction au framework ADK et configuration multi-provider.

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 8 | [ADK-Introduction](Day4-Foundations/Lab8-ADK-Introduction.ipynb) | Architecture ADK, configuration providers |
| 9 | [First-ADK-Agent](Day4-Foundations/Lab9-First-ADK-Agent.ipynb) | Premier agent pour Data Science |

### Day 5 - DS-STAR (Labs 10-12)

Data Science autonome avec l'architecture Planner-Coder-Verifier. Le parcours principal assemble les fondations (10), la boucle Planner-Coder (11), puis l'atelier complet (12) ; les contrats d'orchestration associés au Lab 12 sont présentés séparément ci-dessous.

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 10 | [File-Analyzer](Day5-DS-Star/Lab10-File-Analyzer.ipynb) | Analyse de fichiers hétérogènes | Data Scientists connaissant Python | — |
| 11 | [Planner-Coder-Loop](Day5-DS-Star/Lab11-Planner-Coder-Loop.ipynb) | Boucle itérative multi-agents | Data Scientists connaissant Python | — |
| 12 | [DS-Star-Workshop](Day5-DS-Star/Lab12-DS-Star-Workshop.ipynb) | Application complète | Data Scientists connaissant Python | [12b](#autour-du-lab-12-désignation-et-handoff) · [12c](#autour-du-lab-12-désignation-et-handoff) · [12e](#autour-du-lab-12-persistance-et-usage) · [12d](#autour-du-lab-12-persistance-et-usage) |

## Approfondissements

### Autour du Lab 12: désignation et handoff

Ces labs séparent deux façons de choisir le prochain agent : l'orchestrateur fixe un plan avant l'exécution (C4), tandis que l'agent peut transférer la main pendant un tour (C5). Le Lab 12c compare explicitement ces deux contrats.

| Lab | Notebook | Ce qu'il ajoute | Prérequis conseillé | Contrat et provenance |
|---|---|---|---|---|
| 12b | [Sequential-Orchestration](Day5-DS-Star/Lab12b-Sequential-Orchestration.ipynb) | Contrat C4 : désignation séquentielle, orchestrateur explicite (#14058) | Labs 10-12 pour les rôles du pipeline DS-STAR | Registre EPITA #14058 |
| 12c | [Agent-Handoff](Day5-DS-Star/Lab12c-Agent-Handoff.ipynb) | Contrat C5 : handoff entre agents câblé et observable (#14058) | Lab 12b pour comparer le handoff à la désignation C4 | Registre EPITA #14058 |

### Autour du Lab 12: persistance et usage

La persistance C1b donne à une conversation un historique durable entre ses tours ; le Lab 12d s'appuie sur ce comportement pour rendre mesurable la croissance de l'usage LLM.

| Lab | Notebook | Ce qu'il ajoute | Prérequis conseillé | Contrat et provenance |
|---|---|---|---|---|
| 12e | [Session-Persistence](Day5-DS-Star/Lab12e-Session-Persistence.ipynb) | Contrat C1b : conversation multi-tours persistante (#14058), avec isolation C1 entre conversations | Lab 12 pour le runtime ADK et les tours d'agent | Corpus EPITA #14058 ; le notebook vérifie aussi les tests `test_c1b_history_reaches_next_turn` et `test_c1b_conversations_still_isolate` |
| 12d | [Token-Usage](Day5-DS-Star/Lab12d-Token-Usage.ipynb) | Contrat C6 : traçabilité de la consommation LLM (#14058) | Lab 12e pour la relation entre historique persistant et coût en jetons | Grain #14687 ; registre EPITA #14058 ; `See #14687, #14058` |

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
pip install -r MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Agent-Orchestration/requirements.txt
```

### Configuration

```bash
# Depuis le dossier 07-Agent-Orchestration/
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

Labs 8-12 en séquence. Maîtriser DS-STAR pour automatiser l'analyse de datasets, puis choisir les approfondissements d'orchestration utiles.

1. Labs 8-9 -> architecture ADK, premier agent avec outils
2. Labs 10-12 -> DS-STAR (file analyzer, planner-coder, workshop)
3. Labs 12b-12c -> désignation explicite (C4), puis handoff (C5)
4. Labs 12e-12d -> persistance des sessions (C1b), puis mesure de l'usage (C6)

### Parcours ML engineering (~2 jours)

Labs 13-17 en séquence. MLE-STAR pour les compétitions et le déploiement.

1. Labs 13-15 -> recherche SOTA, ablation, Kaggle
2. Labs 16-17 -> BigQuery/BQML, projet final

### Parcours complet (~4 jours)

Tous les labs (8-17) en séquence, avec les approfondissements 12b, 12c, 12e et 12d après le Lab 12 selon l'ordre indiqué ci-dessus. Le parcours recommandé pour une formation complète.

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
pip install -r 07-Agent-Orchestration/requirements.txt
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

Causes courantes : mauvais chemin `.env` (doit être dans `07-Agent-Orchestration/`), clé API invalide, ou URL base incorrecte pour vLLM.

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

### Quelle version de `google-adk` utiliser ?

Le paquet PyPI `google-adk` et la documentation `adk.dev/2.0` sont la **même lignée 2.x** (GA `2.0.0` le 2026-05-19) : choisir une version revient à choisir un point de cette lignée, pas un fork. Le runtime de la série (`utils/adk_runtime.py`) ne consomme que des API publiques stables — `Agent`, `LiteLlm`, `Runner`, `InMemorySessionService`, `runner.run_async`, lecture des attributs d'`event` — et n'utilise **ni** callbacks (`before_tool_callback`…), **ni** Workflow Graph, **ni** artifacts : les breaking changes mineurs de la lignée 2.x ne l'atteignent pas. Le seul changement de la lignée qui touche `InMemorySessionService` — depuis `2.9.0`, la classe lève `SessionNotFoundError` sur une session inconnue — **n'atteint pas ce runtime** : `run_agent_turn` construit un `InMemorySessionService()` neuf et appelle `create_session` à chaque appel (`utils/adk_runtime.py`, l. 213 et 219), donc aucune session ne survit d'un appel à l'autre et une purge inter-appels y est structurellement impossible. Le point redeviendrait une veille le jour où un service de session **partagé** serait introduit entre deux appels.

Ce que la série installe réellement aujourd'hui : `google-adk==2.8.0`, épinglé dans `requirements.txt` (l. 33). `2.9.0` n'apporte rien que ce runtime consomme, donc aucun bump n'est justifié à ce stade.

L'audit complet de la lignée 2.0.0 → 2.9.0 (changelog analysé motif par motif, **daté du 2026-09-10**) vit dans la lane transiente : [`docs/transients/2026-09-13-adk-migration-2-eval.md`](../../../../docs/transients/2026-09-13-adk-migration-2-eval.md) (audit #14498, verdict « pas de migration immédiate », historique). C'est une **photo datée** : ses entrées décrivent le changelog tel qu'il se lisait ce jour-là et ne sont pas re-vérifiées à chaque lecture. La décision de ne pas bumper ne s'appuie pas sur ce tableau mais sur la construction du service de session dans `utils/adk_runtime.py` (l. 213 et 219), lue à la source.

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

La trame de cette série est la **réduction progressive de l'intervention humaine**. Les [Days 1-3 (06-Data-Agents)](../06-Data-Agents/) vous ont appris à *piloter* un agent ; DS-STAR lui a confié une analyse de bout en bout ; MLE-STAR lui a donné l'initiative de la recherche et de l'optimisation ; les Labs de production l'ont exposé à des contraintes réelles. La frontière entre « outil que l'on dirige » et « collègue que l'on encadre » est précisément ce que ces patterns d'orchestration déplacent — et c'est la compétence que cette série cherche à transmettre.

## Ressources

- [Google ADK Documentation](https://github.com/google/adk-samples)
- [DS-STAR Paper](https://research.google/blog/ds-star-a-state-of-the-art-versatile-data-science-agent/)
- [MLE-STAR Paper](https://research.google/blog/mle-star-a-state-of-the-art-machine-learning-engineering-agents/)
- [LiteLLM Documentation](https://docs.litellm.ai/)

## Licence

Voir la licence du repository principal.

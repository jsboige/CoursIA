# DataScienceWithAgents - Data Science Python avec Agents IA

[← ML (série parente)](../README.md) | [ML.NET (C#) →](../ML.Net/README.md) | [AgenticDataScience (Google ADK) →](AgenticDataScience/README.md)

Formation complète en Data Science Python avec intégration d'agents IA. Combine les fondamentaux NumPy/Pandas avec deux tracks complémentaires : LangChain (3 jours) et Google ADK (4 jours).

Au-delà des bibliothèques classiques, cette formation explore un changement de paradigme : passer de *l'écriture* de code data science à *l'orchestration* d'**agents LLM** qui le produisent et l'exécutent. Après les fondations NumPy/Pandas, le track **LangChain** apprend à construire des agents capables d'interroger un DataFrame, de nettoyer un jeu de données ou de scorer des candidatures ; le track **Google ADK** monte en puissance avec des systèmes multi-agents (boucles planner-coder, frameworks DS-STAR / MLE-STAR) jusqu'à concourir sur des compétitions Kaggle. L'enjeu pédagogique n'est pas seulement technique : il s'agit de comprendre *quand* un agent autonome accélère réellement le travail d'analyse, et *comment* l'encadrer (outils, validation, garde-fous).

## Pourquoi cette série

Le Data Science traditionnel suit un workflow manuel : charger, nettoyer, transformer, modéliser, évaluer. Cette série introduit un **changement de paradigme** : orchestrer des agents LLM qui automatisent ce workflow. L'objectif n'est pas de remplacer le data scientist, mais de comprendre *quand* un agent accélère réellement le travail et *comment* l'encadrer.

La formation couvre deux stacks complémentaires :

| Aspect | Track LangChain (Days 1-3) | Track Google ADK (Days 4-7) |
|--------|---------------------------|----------------------------|
| **Approche** | Agent unique avec tools | Systèmes multi-agents |
| **Framework** | LangChain + OpenAI | Google ADK + LiteLLM |
| **Complexité** | Chains, outils simples | Boucles planner-coder, DS-STAR |
| **Application** | RFP, CV screening, data wrangling | Kaggle, BigQuery, déploiement |
| **Providers** | OpenAI uniquement | Multi-provider (Gemini, vLLM, OpenAI) |

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 19 (7 LangChain + 10 ADK + 2 fondations) |
| Kernel | Python 3.11+ |
| Durée totale | ~7 jours |

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

| Notebook | Contenu | Durée |
|----------|---------|-------|
| [1.2-NumPy](01-PythonForDataScience/notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb) | Arrays, opérations, vectorisation | 45 min |
| [1.3-Pandas](01-PythonForDataScience/notebooks/1.3-Analyse_de_Donnees_avec_Pandas.ipynb) | DataFrames, filtrage, groupby | 60 min |

## Workshop 3 Jours (PythonAgentsForDataScience)

### Day 1 - Révision Python

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

| Catégorie | Technologies |
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
# Créer un fichier .env à la racine du projet
OPENAI_API_KEY=sk-...
```

## Objectifs d'apprentissage

À l'issue de cette série, vous serez capable de :

1. **Construire** un agent LLM avec LangChain (tools, chains, memory) et l'appliquer à des tâches data science concrètes
2. **Évaluer** quand un agent autonome accélère le travail d'analyse vs une approche manuelle
3. **Orchestrer** des systèmes multi-agents avec Google ADK (planner-coder, DS-STAR, MLE-STAR)
4. **Configurer** un pipeline multi-provider (Gemini, OpenAI, vLLM local) via LiteLLM
5. **Déployer** un agent data science en production (BigQuery, BQML, GCP)

## Concepts clés

| Concept | Description |
|---------|-------------|
| **Agent** | LLM + Outils + Prompt + Exécuteur |
| **Tool** | Fonction appelable par l'agent |
| **Chain** | Séquence d'opérations LLM |
| **Memory** | Contexte conversationnel |

## Public cible

- Analystes de données souhaitant intégrer l'IA
- Data scientists intéressés par les agents
- Développeurs Python intermédiaires

## Quel parcours choisir

### Parcours analyste data science (~3 jours)

Labs 1-7 en séquence. Acquérir les bases Pandas, puis construire des agents LangChain pour automatiser l'analyse de données.

1. Lab 1 -> révision Pandas/Matplotlib/Scikit-Learn
2. Labs 2-3 -> agents documentaires (RFP, CV)
3. Labs 4-7 -> data wrangling + agents d'analyse

### Parcours ingénieur ML agentique (~4 jours)

Labs 8-17 en séquence. Monter en complexité avec les frameworks Google ADK et les systèmes multi-agents.

1. Labs 8-9 -> architecture ADK, premier agent
2. Labs 10-12 -> DS-STAR (data science autonome)
3. Labs 13-15 -> MLE-STAR (Kaggle, optimisation)
4. Labs 16-17 -> production (BigQuery, projet final)

### Parcours complet (~7 jours)

Tous les labs en séquence, des fondations NumPy/Pandas jusqu'au déploiement GCP.

### Parcours rapide (~1 jour)

Labs 1 + 6 + 8. Découvrir le pipeline data science, construire un premier agent LangChain, puis un premier agent ADK. Les trois labs les plus représentatifs pour une première prise en main.

## FAQ / Troubleshooting

### `langchain` ou `langchain-openai` échoue à l'import

Vérifier que le bon environnement est activé :

```bash
# vérifier l'environnement
which python  # Linux/Mac
where python  # Windows
# doit pointer vers votre venv, pas le système

# ré-installer si nécessaire
pip install langchain langchain-openai langchain-experimental
```

Si l'erreur persiste, vérifier la version Python (3.10+ requis) : `python --version`.

### Erreur "OPENAI_API_KEY not found" dans les Labs 2-3 et 6-7

Ces labs nécessitent une clé API OpenAI. Créer un fichier `.env` à la racine du projet :

```bash
# À la racine du repo ou à côté des notebooks
echo 'OPENAI_API_KEY=sk-...' > .env
```

Le package `python-dotenv` charge automatiquement ce fichier. Ne JAMAIS committer le fichier `.env` (il est dans `.gitignore`).

### Les agents ADK ne se connectent pas au provider (Labs 8+)

Vérifier la configuration dans le fichier `.env` d'AgenticDataScience :

```bash
# Provider recommandé (clé gratuite)
ACTIVE_PROVIDER=gemini
GEMINI_API_KEY=AIza...

# Ou provider local (pas de clé requise)
ACTIVE_PROVIDER=vllm
VLLM_BASE_URL=http://localhost:8000/v1
```

Si vous utilisez Gemini, obtenir une clé gratuite sur [aistudio.google.com](https://aistudio.google.com).

### `ModuleNotFoundError` pour un package dans un lab

Chaque lab a des dépendances spécifiques. Installer les packages au fur et à mesure :

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

| Concept LangChain | Équivalent ADK |
|-------------------|----------------|
| `LLMChain` | ADK Agent avec instruction |
| `Tool` | ADK FunctionTool |
| `AgentExecutor` | ADK Runner |
| `ConversationBufferMemory` | ADK Session |
| `SequentialChain` | Boucle Planner-Coder |

Le passage se fait naturellement au Lab 8 qui reprend les mêmes concepts avec l'API ADK.

### Le kernel Jupyter n'affiche pas les outputs des agents

Certains agents produisent des outputs longs. Vérifier :

1. La cellule n'est pas en timeout (augmenter le timeout du kernel)
2. Le provider répond (tester avec un appel simple : `client.chat.completions.create(...)`)
3. Les prints intermédiaires sont flushés : `print(..., flush=True)`

## Ressources

- [Pandas Documentation](https://pandas.pydata.org/docs/)
- [LangChain Documentation](https://python.langchain.com/)
- [OpenAI Cookbook](https://cookbook.openai.com/)

## Track AgenticDataScience (Days 4-7)

Track avancé intégrant les frameworks Google ADK (DS-STAR, MLE-STAR) avec support multi-provider.

### Day 4 - ADK Foundations (Labs 8-9)

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 8 | [ADK-Introduction](AgenticDataScience/Day4-Foundations/Lab8-ADK-Introduction.ipynb) | Architecture ADK, configuration providers |
| 9 | [First-ADK-Agent](AgenticDataScience/Day4-Foundations/Lab9-First-ADK-Agent.ipynb) | Premier agent pour Data Science |

### Day 5 - DS-STAR (Labs 10-12)

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 10 | [File-Analyzer](AgenticDataScience/Day5-DS-Star/Lab10-File-Analyzer.ipynb) | Analyse de fichiers hétérogènes |
| 11 | [Planner-Coder-Loop](AgenticDataScience/Day5-DS-Star/Lab11-Planner-Coder-Loop.ipynb) | Boucle itérative multi-agents |
| 12 | [DS-Star-Workshop](AgenticDataScience/Day5-DS-Star/Lab12-DS-Star-Workshop.ipynb) | Application complète |

### Day 6 - MLE-STAR (Labs 13-15)

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 13 | [Web-Search-SOTA](AgenticDataScience/Day6-MLE-Star/Lab13-Web-Search-SOTA.ipynb) | Recherche de modèles SOTA |
| 14 | [Ablation-Refinement](AgenticDataScience/Day6-MLE-Star/Lab14-Ablation-Refinement.ipynb) | Optimisation ciblée |
| 15 | [Kaggle-Challenge](AgenticDataScience/Day6-MLE-Star/Lab15-Kaggle-Challenge.ipynb) | Compétition Kaggle |

### Day 7 - Production (Labs 16-17)

| Lab | Notebook | Objectif |
|-----|----------|----------|
| 16 | [Data-Science-Agent](AgenticDataScience/Day7-Production/Lab16-Data-Science-Agent.ipynb) | Agent BigQuery/BQML |
| 17 | [Final-Project](AgenticDataScience/Day7-Production/Lab17-Final-Project.ipynb) | Projet intégré |

### Technologies AgenticDataScience

| Catégorie | Technologies |
|-----------|--------------|
| **Abstraction** | LiteLLM (multi-provider) |
| **Google ADK** | google-adk, google-generativeai |
| **Providers** | Gemini 3.1, vLLM, OpenAI, OpenRouter |
| **Cloud (Day 7)** | BigQuery, Vertex AI, BQML |

Documentation complète : [AgenticDataScience/README.md](AgenticDataScience/README.md)

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Cette série vous a fait traverser un **changement de posture** en data science : passer de *l'écriture* du code d'analyse à *l'orchestration* d'agents LLM qui le produisent et l'exécutent. L'arc pédagogique :

- **Les fondations, volontairement manuelles** — NumPy (vectorisation) et Pandas (DataFrame, groupby, nettoyage) d'abord pratiqués à la main. Cette base n'est pas un préalable accessoire : c'est le référent qui rend *jugeable* le travail de l'agent. On ne peut évaluer ce qu'un agent produit sur un DataFrame que si l'on sait soi-même le manipuler — d'où la règle des 80/20 (CrowdFlower, 2016) qui ouvre le Lab 4 : la préparation reste le cœur du métier, l'agent l'accélère sans l'effacer.
- **Le track LangChain — l'agent unique outillé (Days 1-3)** — on assemble les quatre composants d'un agent (LLM + outils + prompt + orchestrateur), puis on l'applique à des tâches documentaires (parsing d'appel d'offre, scoring de CV) et d'analyse (wrangling, classification, agent DataFrame). Deux paradigmes canoniques structurent cette track : **LCEL** (composition par tube `prompt | llm`) pour les chaînes, et **ReAct** (boucle Pensée→Action→Observation) couplée au **tool-calling** pour le premier agent ; le `create_pandas_dataframe_agent` concrétise **CodeAct** (l'agent écrit et exécute lui-même son Python). L'enjeu n'est pas la magie du LLM mais la *qualité du prompt* et du *schéma de sortie* (JSON structuré).
- **Le track Google ADK — les systèmes multi-agents (Days 4-7)** — on monte en abstraction : du single-agent on passe à des *systèmes* (boucles planner-coder-verifier), puis aux architectures SOTA (DS-STAR pour la data science, MLE-STAR pour l'ingénierie ML), jusqu'à concourir sur Kaggle (MLE-bench) et déployer en production (BigQuery, Vertex AI, BQML). La question bascule : ce n'est plus « comment coder cette analyse ? » mais « comment concevoir un *système d'agents* qui l'exécute, la valide et la raffine ? ».
- **La finesse** — la série ne vend pas l'agent autonome comme une solution universelle. Chaque lab pose la question du *cadre* : quels outils exposer, comment valider la sortie, quand l'agent accélère réellement *vs* quand il hallucine ou dérive. Le survey sur l'hallucination (Lab 17) et la méthodologie d'ablation (Lab 14) ancrent cette lucidité.

La thèse est honnête : les agents LLM ne remplacent pas le data scientist, ils *reconfigurent* son métier — de l'exécution vers l'orchestration, la spécification et la validation. Le savoir-faire Pandas/scikit-learn reste le socle ; ce qui change, c'est la *granularité* à laquelle on pilote l'analyse.

### Prochaines étapes

- **Approfondir le ML sous-jacent** : la série [ML](../README.md) (et son pendant C# [ML.Net](../ML.Net/README.md)) reprend les algorithmes (LightGBM, SSA, évaluation PFI/ROC) sous l'angle de l'implémentation — utile pour comprendre ce que l'agent exécute quand il génère du code scikit-learn.
- **Aller vers l'évaluation et la robustesse** : les Labs 13-15 (Web-Search-SOTA, Ablation-Refinement, Kaggle-Challenge) introduisent l'évaluation rigoureuse des agents ML (MLE-bench, métriques cross-compétition) ; le prolongement naturel est la **robustesse multi-seed** et la **walk-forward validation**, traitées dans le pipeline [QuantConnect](../../QuantConnect/README.md).
- **Franchir le cap production** : le Day 7 (BigQuery, BQML, Vertex AI) ouvre sur le déploiement réel. Le pont vers [GenAI](../../GenAI/README.md) relie ces agents data aux pipelines de génération (image, audio, texte) et aux architectures Qwen/Lumina auto-hébergées.
- Pour la pratique : reprenez le Lab 7 (agent DataFrame) et posez-lui une question qu'il *ne peut pas* répondre avec les seules colonnes présentes — comment réagit-il ? Confrontez cette limite au Lab 11 (boucle planner-coder) : qu'apporte vraiment le multi-agent ? C'est la tension vivante de la série : la puissance de l'agent *vs* la nécessité de l'encadrer.

### Le fil rouge

Le data science agentique propose un changement de regard : ne plus demander « comment coder cette analyse ? » mais **« comment la spécifier assez clairement pour qu'un agent LLM la code, l'exécute et la valide à ma place ? »**. La série vous a donné les fondations (NumPy/Pandas), l'agent unique outillé (LangChain, ReAct, tool-calling, CodeAct) et les systèmes multi-agents (ADK, DS-STAR/MLE-STAR, production GCP) — en gardant à l'esprit que la valeur d'un agent se mesure moins à ce qu'il *produit* qu'à la *qualité du cadre* (outils, prompts, validation) dans lequel il opère.

---

## Licence

Voir la licence du repository principal.

# CoursIA

Bienvenue dans le depot **CoursIA**, plateforme educative complete pour l'apprentissage de l'intelligence artificielle en C# et Python.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## Table des matieres

- [Introduction](#introduction)
- [Cartographie complete](#cartographie-complete)
- [Series de notebooks](#series-de-notebooks)
- [Configuration et API Keys](#configuration-et-api-keys)
- [Kernels Jupyter](#kernels-jupyter)
- [Outils externes](#outils-externes)
- [Mise en route](#mise-en-route)
- [Infrastructure Docker](#infrastructure-docker)
- [Scripts et validation](#scripts-et-validation)
- [Outils Claude Code](#outils-claude-code)
- [Contribution](#contribution)

## Introduction

Ce depot contient **290+ notebooks Jupyter** interactifs couvrant :
- **IA Symbolique** : Logiques formelles, argumentation, verification formelle (Lean 4, Tweety, Z3)
- **Probabilites** : Inference bayesienne, modeles graphiques (Infer.NET)
- **Theorie des jeux** : Nash, jeux evolutionnaires, cooperatifs, CFR, OpenSpiel
- **Machine Learning** : ML.NET, algorithmes genetiques
- **IA Generative** : OpenAI, LLMs, generation d'images, audio et video (DALL-E, FLUX, Qwen, SD3.5, Whisper, MusicGen, AnimateDiff)
- **Trading Algorithmique** : QuantConnect LEAN, ML/DL/RL pour strategies de trading

Les notebooks sont en **C# (.NET Interactive)**, **Python** et **Lean 4**, avec une documentation pedagogique complete.

## Cartographie complete

### Structure du depot

```
CoursIA/
├── MyIA.AI.Notebooks/           # 255+ notebooks interactifs
│   ├── GenAI/                   # IA Generative (87+ notebooks)
│   │   ├── 00-GenAI-Environment/# Setup et configuration (6 notebooks)
│   │   ├── Image/               # Generation d'images (19 notebooks)
│   │   │   ├── 01-Foundation/   # DALL-E 3, GPT-5, Forge
│   │   │   ├── 02-Advanced/     # Qwen, FLUX, SD3.5, Z-Image
│   │   │   ├── 03-Orchestration/# Multi-modeles, workflows
│   │   │   └── 04-Applications/ # Production, contenu educatif
│   │   ├── Audio/               # Speech, TTS, musique (16 notebooks)
│   │   │   ├── 01-Foundation/   # OpenAI TTS/Whisper, operations audio
│   │   │   ├── 02-Advanced/     # Voice cloning, MusicGen, Demucs
│   │   │   ├── 03-Orchestration/# Multi-modeles audio, temps reel
│   │   │   └── 04-Applications/ # Contenu educatif, transcription, sync
│   │   ├── Video/               # Generation et comprehension (16 notebooks)
│   │   │   ├── 01-Foundation/   # Operations, GPT-5 video, Qwen-VL, AnimateDiff
│   │   │   ├── 02-Advanced/     # HunyuanVideo, LTX, Wan, SVD
│   │   │   ├── 03-Orchestration/# Multi-modeles video, ComfyUI
│   │   │   └── 04-Applications/ # Video educative, workflows, production
│   │   ├── Texte/               # LLMs et generation texte (10 notebooks)
│   │   ├── SemanticKernel/      # Microsoft Semantic Kernel (14 notebooks)
│   │   └── Vibe-Coding/         # Claude Code et Roo Code tutorials
│   │
│   ├── SymbolicAI/              # IA Symbolique (47+ notebooks)
│   │   ├── Tweety/              # TweetyProject - 10 notebooks
│   │   ├── Lean/                # Lean 4 - 10 notebooks
│   │   ├── Argument_Analysis/   # Analyse argumentative - 6 notebooks
│   │   └── Planners/            # Fast-Downward, PDDL
│   │
│   ├── GameTheory/              # Theorie des jeux (26 notebooks)
│   │   ├── GameTheory-1 to 17   # Notebooks principaux
│   │   └── *b, *c variants      # Lean + Python side tracks
│   │
│   ├── Probas/Infer/            # Infer.NET - 20 notebooks
│   ├── Sudoku/                  # Resolution Sudoku (11 notebooks)
│   ├── Search/                  # Recherche et optimisation (5 notebooks)
│   ├── ML/                      # Machine Learning (14 notebooks)
│   ├── RL/                      # Reinforcement Learning (3 notebooks)
│   ├── QuantConnect/            # Trading algorithmique + AI (27 notebooks Python)
│   ├── IIT/                     # PyPhi - Information integree (1 notebook)
│   ├── Probas/                  # Probabilites (22 notebooks)
│   ├── EPF/                     # Devoirs etudiants (4 notebooks)
│   └── Config/                  # Configuration API (settings.json)
│
├── .claude/                     # Configuration Claude Code
│   ├── agents/                  # 10 agents specialises
│   └── commands/                # 6 skills (commandes slash)
│
├── scripts/                     # Scripts utilitaires
│   ├── verify_notebooks.py      # Verification multi-famille
│   ├── extract_notebook_skeleton.py  # Extraction structure
│   └── genai-stack/             # Validation GenAI
│
├── docker-configurations/       # Infrastructure Docker GPU
│   ├── services/
│   │   ├── comfyui-qwen/        # ComfyUI + Qwen Image Edit
│   │   ├── orchestrator/        # Multi-services (FLUX, SD3.5)
│   │   ├── vllm-zimage/         # Z-Image/Lumina
│   │   └── forge-turbo/         # Forge SD
│   └── shared/                  # Modeles et cache partages
│
├── GradeBookApp/                # Systeme de notation etudiants
├── notebook-infrastructure/     # Papermill automation
└── MyIA.AI.Shared/              # Bibliotheque C# partagee
```

### Statistiques globales

| Categorie | Notebooks | Kernels | Duree estimee | API requise |
|-----------|-----------|---------|---------------|-------------|
| **SymbolicAI** | 47+ | Python, Lean 4 | ~25h | OpenAI (optionnel) |
| **GameTheory** | 26 | Python, Lean 4 | ~18h30 | OpenAI (optionnel) |
| **Infer.NET** | 20 | .NET C# | ~17h | - |
| **GenAI** | 87+ | Python | ~75h | OpenAI/Anthropic |
| **Sudoku** | 11 | C#, Python | ~2h | - |
| **Search** | 5 | C#, Python | ~1h10 | - |
| **ML** | 14 | C#, Python | ~4h | - |
| **RL** | 3 | Python | ~2h | - |
| **QuantConnect** | 27 | Python | ~30h | QuantConnect (gratuit) |
| **IIT** | 1 | Python | ~1h30 | - |
| **Total** | **290+** | **Mixed** | **~180h** | - |

## Series de notebooks

### SymbolicAI - IA Symbolique

Decouverte des logiques formelles et de l'argumentation computationnelle. Cette serie vous fera explorer les systemes de raisonnement automatique, de la logique propositionnelle aux frameworks d'argumentation de Dung, en passant par la verification de theoremes avec Lean 4. Vous apprendrez a utiliser **TweetyProject** (bibliotheque Java via JPype) pour manipuler des bases de connaissances, calculer des extensions d'argumentation, et modeliser des dialogues multi-agents. La serie couvre egalement les extensions avancees (ASPIC+, DeLP, ADF), la revision de croyances AGM, et les systemes de preferences.

**47+ notebooks** couvrant les logiques formelles, l'argumentation computationnelle et la verification formelle.

| Serie | Notebooks | Contenu | Prerequis | README |
|-------|-----------|---------|-----------|--------|
| **Tweety** | 10 | TweetyProject, logiques PL/FOL/DL, argumentation Dung, ASPIC+ | JDK 17+ (auto) | [README](MyIA.AI.Notebooks/SymbolicAI/Tweety/README.md) |
| **Lean** | 11 | Lean 4, types dependants, tactiques, Mathlib, LLM integration | WSL, elan | [README](MyIA.AI.Notebooks/SymbolicAI/Lean/README.md) |
| **Argument_Analysis** | 6 | Analyse argumentative multi-agents avec Semantic Kernel | OpenAI API | [README](MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/README.md) |
| **Planners** | 1 | Fast-Downward, planification PDDL | Python | [README](MyIA.AI.Notebooks/SymbolicAI/Planners/README.md) |
| **Autres** | 14+ | Z3, OR-Tools, RDF.NET | Varies | - |

**Focus sur Lean 4** : Cette sous-serie vous initie a la verification formelle avec Lean 4, un assistant de preuves et langage de programmation fonctionnel base sur la theorie des types dependants. Vous progresserez des fondements (types dependants, isomorphisme de Curry-Howard) jusqu'aux tactiques avancees de Mathlib, puis decouvrirez l'etat de l'art de l'assistance par LLMs (LeanCopilot, AlphaProof) et les agents autonomes pour la preuve mathematique. Note : necessite WSL sous Windows.

**Notebooks Tweety (detail)** :

| Notebook | Contenu | Outils externes |
|----------|---------|-----------------|
| Tweety-1-Setup | JDK, JPype, libs | - |
| Tweety-2-Basic-Logics | PL, FOL, SAT4J, pySAT | pySAT |
| Tweety-3-Advanced-Logics | DL, Modal, QBF | SPASS (admin req.) |
| Tweety-4-Belief-Revision | CrMas, MUS, MaxSAT | MARCO |
| Tweety-5-Abstract-Argumentation | Dung, semantiques | - |
| Tweety-6-Structured-Argumentation | ASPIC+, DeLP, ASP | Clingo |
| Tweety-7a-Extended-Frameworks | ADF, Bipolar, WAF | - |
| Tweety-7b-Ranking-Probabilistic | Ranking semantics | - |
| Tweety-8-Agent-Dialogues | Protocoles de dialogue | - |
| Tweety-9-Preferences | Voting, social choice | - |

[README SymbolicAI](MyIA.AI.Notebooks/SymbolicAI/README.md)

### GameTheory - Theorie des Jeux

Des jeux statiques aux strategies multi-agent. Cette serie couvre les fondamentaux de la theorie des jeux : equilibres de Nash, strategies mixtes, jeux evolutionnaires et repetes. Vous implementerez des algorithmes comme CFR (Counterfactual Regret Minimization) avec Nashpy et OpenSpiel, tout en decouvrant les preuves formelles avec Lean 4 pour une comprehension mathematique approfondie.

**26 notebooks** (17 principaux + 9 side tracks) combinant Python et Lean 4.

| Partie | Notebooks | Contenu | Kernel |
|--------|-----------|---------|--------|
| **Fondations** | 1-6 | Forme normale, Nash, minimax, jeux evolutionnaires | Python |
| **Jeux dynamiques** | 7-12 | Forme extensive, backward induction, jeux bayesiens | Python |
| **Avances** | 13-17 | CFR, jeux differentiels, cooperatifs, mechanism design, MARL | Python + OpenSpiel |
| **Side tracks b** | 2b, 4b, 8b, 15b, 16b | Formalisations Lean 4 | Lean 4 (WSL) |
| **Side tracks c** | 2c, 4c, 8c, 15c, 16c | Approfondissements Python | Python |

[README GameTheory](MyIA.AI.Notebooks/GameTheory/README.md)

### Probas - Programmation Probabiliste

Programmation probabiliste et inference bayesienne. Avec Infer.NET de Microsoft, vous apprendrez a definir des modeles probabilistes, propager l'incertitude et mettre a jour vos croyances face a de nouvelles observations. La serie couvre les distributions fondamentales (Gaussian, Beta, Dirichlet), les reseaux bayesiens et la theorie de la decision sous incertitude.

**22 notebooks** couvrant l'inference bayesienne avec Infer.NET (C#) et Pyro (Python).

| Section | Notebooks | Kernel | Contenu |
|---------|-----------|--------|---------|
| **Racine** | 2 | Python/C# | Infer-101 (intro), Pyro_RSA_Hyperbole (pragmatique) |
| **Infer/ 1-13** | 13 | C# | Fondamentaux, modeles classiques, debugging |
| **Infer/ 14-20** | 7 | C# | Theorie de la decision bayesienne |

[README Probas](MyIA.AI.Notebooks/Probas/README.md) | [README Infer](MyIA.AI.Notebooks/Probas/Infer/README.md)

### Sudoku - Resolution par Contraintes

Une approche comparative des algorithmes de resolution. Ce qui rend cette serie unique : le meme probleme resolu avec six techniques differentes ! Vous comparerez le backtracking naif, les algorithmes genetiques, la programmation par contraintes (OR-Tools), les solveurs SMT (Z3), et meme une approche probabiliste (Infer.NET). Ideal pour comprendre les compromis performance/complexite de chaque paradigme.

**11 notebooks** (7 C#, 4 Python) illustrant differentes approches algorithmiques.

| Approche | Notebooks | Technologies | Kernel |
|----------|-----------|--------------|--------|
| **Backtracking** | 1, Python | MRV, recherche exhaustive | C#, Python |
| **Genetique** | 2, Python | GeneticSharp, PyGAD | C#, Python |
| **Contraintes** | 3, Python | OR-Tools CP/SAT/MIP | C#, Python |
| **SMT** | 4, Python | Z3, bitvectors | C#, Python |
| **Couverture exacte** | 5, Python | Dancing Links (DLX) | C#, Python |
| **Probabiliste** | 6 | Infer.NET | C# |

**Note** : Les notebooks C# utilisent `#!import` et necessitent une execution cellule par cellule (Papermill incompatible).

[README Sudoku](MyIA.AI.Notebooks/Sudoku/README.md)

### Search - Recherche et Optimisation

Algorithmes classiques et metaheuristiques d'optimisation. De la recherche aveugle (BFS, DFS) aux heuristiques informees (A*, Hill Climbing) en passant par le recuit simule et les algorithmes genetiques. Les notebooks appliquent ces concepts a des problemes concrets : detection de bords dans une image, optimisation de portefeuille financier, satisfaction de contraintes.

**5 notebooks** sur les algorithmes de recherche et les metaheuristiques.

| Notebook | Kernel | Contenu |
|----------|--------|---------|
| CSPs_Intro | Python | Programmation par contraintes, AC-3, N-Queens, Min-Conflicts |
| Exploration | Python | BFS, DFS, A*, Hill Climbing, Simulated Annealing |
| GeneticSharp-EdgeDetection | C# | Detection de bords avec GeneticSharp |
| Portfolio_Optimization | C# | Optimisation de portefeuille financier |
| PyGad-EdgeDetection | Python | Detection de bords avec PyGAD |

[README Search](MyIA.AI.Notebooks/Search/README.md)

### GenAI - IA Generative

De l'appel API a l'orchestration de workflows complexes. Cette serie vous emmene du premier prompt avec l'API OpenAI jusqu'a la construction d'applications multi-modeles. Vous explorerez la generation d'images (DALL-E 3, FLUX, Qwen, SD 3.5), d'audio (TTS, STT, musique) et de video, le prompt engineering avance, les outputs structures, le RAG, et l'orchestration avec Microsoft Semantic Kernel.

**87+ notebooks** organises en plusieurs sous-domaines.

| Sous-domaine | Notebooks | Contenu | Services requis |
|--------------|-----------|---------|-----------------|
| **00-Environment** | 6 | Setup, Docker, API, validation, deploiement local | - |
| **Image/** | 19 | Generation d'images (4 niveaux) | OpenAI/Docker GPU |
| **Audio/** | 16 | Speech, TTS, musique, separation (4 niveaux) | OpenAI/GPU local |
| **Video/** | 16 | Operations, comprehension, generation (4 niveaux) | OpenAI/GPU local |
| **Texte/** | 10 | OpenAI, Prompts, Structured Outputs, RAG, Reasoning, Production | OpenAI API |
| **SemanticKernel/** | 14 | SK Fundamentals a MCP, NotebookMaker, templates | OpenAI API |
| **Vibe-Coding/** | 5+ | Notebooks CLI Claude Code + ateliers Roo Code | Claude/Roo |

**Structure Image/** :

| Niveau | Contenu |
|--------|---------|
| **01-Foundation** | DALL-E 3, GPT-5, Forge SD-XL Turbo, Qwen |
| **02-Advanced** | Qwen Image Edit 2509, FLUX, SD 3.5, Z-Image/Lumina |
| **03-Orchestration** | Comparaison multi-modeles, workflows, optimisation |
| **04-Applications** | Contenu educatif, workflows creatifs, production |

**Structure Audio/** :

| Niveau | Contenu |
|--------|---------|
| **01-Foundation** | OpenAI TTS, Whisper STT, operations audio (librosa, pydub), Whisper local, Kokoro TTS |
| **02-Advanced** | Chatterbox TTS, XTTS voice cloning, MusicGen, Demucs separation |
| **03-Orchestration** | Multi-model comparison, pipelines audio, temps reel (Realtime API) |
| **04-Applications** | Contenu educatif, transcription pipeline, composition musicale, sync A/V |

**Structure Video/** :

| Niveau | Contenu |
|--------|---------|
| **01-Foundation** | Operations video (moviepy, ffmpeg), GPT-5 understanding, Qwen-VL, ESRGAN, AnimateDiff |
| **02-Advanced** | HunyuanVideo, LTX-Video, Wan, SVD image-to-video |
| **03-Orchestration** | Multi-model comparison, workflows video, ComfyUI Video |
| **04-Applications** | Video educative, workflows creatifs, Sora API, production pipeline |

[README GenAI](MyIA.AI.Notebooks/GenAI/README.md)

### IIT - Integrated Information Theory

**1 notebook** sur PyPhi et la theorie de l'information integree.

| Notebook | Contenu | Duree |
|----------|---------|-------|
| [Intro_to_PyPhi](MyIA.AI.Notebooks/IIT/Intro_to_PyPhi.ipynb) | TPM, Phi, CES, Causation actuelle, Macro-subsystemes | ~90 min |

[README IIT](MyIA.AI.Notebooks/IIT/README.md)

### ML - Machine Learning

**14 notebooks** couvrant ML.NET (C#) et Python Data Science avec agents IA.

| Section | Notebooks | Contenu |
|---------|-----------|---------|
| **ML.NET** | 5 | Introduction, Features, Entrainement, AutoML, Evaluation |
| **Python Foundations** | 2 | NumPy, Pandas |
| **AI Agents Workshop** | 7 | RFP Analysis, CV Screening, Data Wrangling, First Agent |

[README ML](MyIA.AI.Notebooks/ML/README.md)

### RL - Reinforcement Learning

**3 notebooks** sur Stable Baselines3 et l'apprentissage par renforcement.

| Notebook | Contenu | Duree |
|----------|---------|-------|
| stable_baseline_1 | Introduction PPO, CartPole | ~30 min |
| stable_baseline_2 | Wrappers, sauvegarde, callbacks | ~40 min |
| stable_baseline_3 | HER, goal-conditioned RL, SAC/DDPG | ~45 min |

[README RL](MyIA.AI.Notebooks/RL/README.md)

### QuantConnect - Trading Algorithmique + AI

Trading algorithmique avec ML/DL/RL et LLMs. Base sur le framework LEAN de QuantConnect, cette serie progresse des fondamentaux du backtesting jusqu'aux strategies avancees integrant machine learning, deep learning et meme des LLMs pour l'analyse de sentiment. Le free tier cloud permet de tester sans infrastructure locale.

**27 notebooks Python** sur le trading algorithmique avec QuantConnect LEAN, incluant ML/DL/RL/LLM.

| Phase | Notebooks | Contenu |
|-------|-----------|---------|
| **Fondations LEAN** | 01-04 | Setup, Platform Fundamentals, Data Management, Research |
| **Universe & Assets** | 05-08 | Universe Selection, Options, Futures/Forex, Multi-Asset |
| **Trading Avance** | 09-12 | Order Types, Risk Management, Indicators, Backtesting |
| **Algorithm Framework** | 13-15 | Alpha Models, Portfolio Construction, Optimization |
| **Data Alternatives** | 16-17 | Alternative Data, Sentiment Analysis |
| **ML/DL/AI** | 18-27 | Features, Classification, Regression, Deep Learning, RL, LLM |

**Caracteristiques** :
- Cloud-first (QuantConnect free tier)
- 9 notebooks dedies ML/DL/RL/LLM
- Production-ready (deployment live)

[README QuantConnect](MyIA.AI.Notebooks/QuantConnect/README.md) | [Getting Started](MyIA.AI.Notebooks/QuantConnect/GETTING-STARTED.md)

## Configuration et API Keys

### Fichiers de configuration par famille

| Famille | Fichier .env | Variables cles |
|---------|--------------|----------------|
| **GenAI** | `MyIA.AI.Notebooks/GenAI/.env` | `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `COMFYUI_API_TOKEN` |
| **Argument_Analysis** | `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/.env` | `OPENAI_API_KEY`, `GLOBAL_LLM_SERVICE`, `BATCH_MODE` |
| **Lean** | `MyIA.AI.Notebooks/SymbolicAI/Lean/.env` | `OPENAI_API_KEY`, `GITHUB_TOKEN`, `LEAN_VERSION` |
| **GameTheory** | `MyIA.AI.Notebooks/GameTheory/.env` | `BATCH_MODE`, `OPENSPIEL_NUM_THREADS` |
| **QuantConnect** | `MyIA.AI.Notebooks/QuantConnect/.env` | `QC_USER_ID`, `QC_API_TOKEN`, `QC_ORG_ID` |
| **C# Notebooks** | `MyIA.AI.Notebooks/Config/settings.json` | `apikey`, `model`, `type` (openai/azure) |
| **Docker ComfyUI** | `docker-configurations/services/comfyui-qwen/.env` | `CIVITAI_TOKEN`, `HF_TOKEN`, `COMFYUI_BEARER_TOKEN` |

### Configuration initiale

```bash
# GenAI
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env
# Editer et ajouter: OPENAI_API_KEY, ANTHROPIC_API_KEY

# Argument Analysis
cp MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/.env.example MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/.env
# Editer et ajouter: OPENAI_API_KEY

# Lean (pour notebooks 7-10)
cp MyIA.AI.Notebooks/SymbolicAI/Lean/.env.example MyIA.AI.Notebooks/SymbolicAI/Lean/.env
# Editer et ajouter: OPENAI_API_KEY, GITHUB_TOKEN

# GameTheory
cp MyIA.AI.Notebooks/GameTheory/.env.example MyIA.AI.Notebooks/GameTheory/.env

# C# Notebooks
cp MyIA.AI.Notebooks/Config/settings.json.openai-example MyIA.AI.Notebooks/Config/settings.json
# Editer et ajouter: apikey

# Docker ComfyUI
cp docker-configurations/services/comfyui-qwen/.env.example docker-configurations/services/comfyui-qwen/.env
# Editer et ajouter: CIVITAI_TOKEN, HF_TOKEN
```

### Variables d'environnement detaillees

**GenAI (.env.template)** :
```bash
# API principale
OPENAI_API_KEY=sk-...
ANTHROPIC_API_KEY=sk-ant-...
OPENROUTER_API_KEY=sk-or-...  # Alternative multi-modeles

# Services Docker
COMFYUI_API_URL=http://localhost:8188
COMFYUI_API_TOKEN=...

# Configuration
DEFAULT_VISION_MODEL=gpt-5-mini
GENAI_TIMEOUT_SECONDS=120
GENAI_MAX_RETRIES=3
```

**Lean (.env.example)** :
```bash
# LLM Integration (notebooks 7-10)
OPENAI_API_KEY=sk-...
ANTHROPIC_API_KEY=sk-ant-...

# LeanDojo (notebook 10)
GITHUB_TOKEN=ghp_...

# Lean configuration
LEAN_VERSION=4.3.0
LEAN_TIMEOUT=30
```

## Kernels Jupyter

### Kernels par famille

| Famille | Kernel | Installation |
|---------|--------|--------------|
| **Python notebooks** | `python3` | Conda `mcp-jupyter-py310` |
| **C# notebooks** | `.net-csharp` | `dotnet tool install -g Microsoft.dotnet-interactive` |
| **Lean 4** | `lean4_jupyter` | Via `elan` (WSL uniquement) |

### Installation des kernels

**Python** :
```bash
python -m venv venv
venv\Scripts\activate  # Windows
pip install jupyter ipykernel
python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"
```

**.NET Interactive** :
```bash
dotnet tool install -g Microsoft.dotnet-interactive
dotnet interactive jupyter install
```

**Lean 4 (WSL uniquement)** :
```bash
# Dans WSL
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
pip install lean4_jupyter
python -m lean4_jupyter.install
```

### Limitations kernels

| Probleme | Impact | Contournement |
|----------|--------|---------------|
| **Papermill + `#!import`** | Notebooks C# avec imports bloquent | Execution cellule par cellule |
| **Lean sur Windows** | signal.SIGPIPE non supporte | Utiliser WSL |
| **Cold start .NET** | Premier demarrage 30-60s | Relancer apres timeout |

## Outils externes

### Outils par famille

| Outil | Version | Notebooks | Installation |
|-------|---------|-----------|--------------|
| **Z3 SMT Solver** | 4.12+ | Sudoku, SymbolicAI, Search | `pip install z3-solver` |
| **OR-Tools** | 9.8+ | Sudoku, Search, SymbolicAI | `pip install ortools` |
| **Tweety** | 1.28 | Tweety series | Auto-telecharge (JARs) |
| **JDK** | 17+ | Tweety, Argument_Analysis | Auto-telecharge (Zulu portable) |
| **PyPhi** | 1.2+ | IIT | `pip install pyphi` |
| **Lean 4** | 4.3+ | Lean, GameTheory | Via `elan` (WSL) |
| **Mathlib4** | Latest | Lean 6+ | Auto avec `lake` |
| **OpenSpiel** | 1.4+ | GameTheory 13-15 | `pip install open_spiel` |
| **Infer.NET** | 0.4+ | Probas/Infer | Via NuGet |
| **Clingo** | 5.6+ | Tweety-6 | Installation manuelle |
| **pySAT** | 1.8+ | Tweety-2 | `pip install python-sat` |

### Outils optionnels

| Outil | Usage | Note |
|-------|-------|------|
| **SPASS** | Logique modale (Tweety-3) | Requiert droits admin Windows |
| **EProver** | FOL prover | Linux uniquement |
| **MARCO** | MUS enumeration | Avec Z3 |
| **Fast-Downward** | Planification PDDL | Auto-compilation |

## Mise en route

### Prerequis

- **Python 3.10+** avec pip
- **.NET 9.0 SDK** (pour notebooks C#)
- **Visual Studio Code** avec extensions Python, Jupyter, .NET Interactive
- **WSL** (recommande pour Lean et certains outils)
- **Docker + GPU** (optionnel, pour GenAI avance)

### Installation rapide

```bash
# 1. Cloner le depot
git clone https://github.com/jsboige/CoursIA.git
cd CoursIA

# 2. Environnement Python
python -m venv venv
venv\Scripts\activate  # Windows
pip install jupyter openai anthropic python-dotenv

# 3. Kernel Python
python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"

# 4. Packages .NET
dotnet restore MyIA.CoursIA.sln

# 5. Configuration API (choisir selon besoins)
cp MyIA.AI.Notebooks/Config/settings.json.openai-example MyIA.AI.Notebooks/Config/settings.json
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env
# Editer les fichiers et ajouter les cles API
```

### Installation par famille

**Sudoku/Search** (aucune config requise) :
```bash
pip install z3-solver ortools numpy matplotlib
```

**Tweety** (JDK auto-telecharge) :
```bash
pip install jpype1 python-sat
# Executer Tweety-1-Setup.ipynb pour telecharger JDK et JARs
```

**Lean** (WSL requis) :
```bash
# Dans WSL
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
pip install lean4_jupyter openai anthropic
python -m lean4_jupyter.install
# Valider: python MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/validate_lean_setup.py
```

**GameTheory** :
```bash
pip install numpy scipy matplotlib nashpy open_spiel networkx
cp MyIA.AI.Notebooks/GameTheory/.env.example MyIA.AI.Notebooks/GameTheory/.env
```

**GenAI** (Docker GPU recommande) :
```bash
pip install -r MyIA.AI.Notebooks/GenAI/requirements.txt
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env
# Editer .env avec API keys
```

### Parcours d'apprentissage suggere

1. **ML** - Introduction au Machine Learning (ML.NET et Python)
2. **Sudoku** - Algorithmes de resolution (backtracking, contraintes)
3. **Search** - Recherche et optimisation
4. **RL** - Reinforcement Learning avec Stable Baselines3
5. **SymbolicAI/Tweety** - Logiques formelles et argumentation
6. **Probas** - Inference bayesienne (Infer.NET, Pyro)
7. **IIT** - Theorie de l'information integree (PyPhi)
8. **GameTheory** - Theorie des jeux
9. **SymbolicAI/Lean** - Verification formelle (WSL requis)
10. **GenAI** - IA generative (API keys requises)

## Infrastructure Docker

### Services disponibles

| Service | Port | GPU | VRAM | Description |
|---------|------|-----|------|-------------|
| **ComfyUI-Qwen** | 8188 | Oui | ~29GB | Qwen Image Edit 2509 |
| **FLUX.1-dev** | 8189 | Oui | ~10GB | Text-to-image |
| **Stable Diffusion 3.5** | 8190 | Oui | ~12GB | Image generation |
| **Z-Image/Lumina** | 8001 | Oui | ~10GB | Lumina-Next-SFT |
| **Orchestrator** | 8090 | Non | - | Service management |

### Demarrage rapide

```bash
# ComfyUI seul
cd docker-configurations/services/comfyui-qwen
cp .env.example .env
docker-compose up -d

# Multi-services (orchestrator)
cd docker-configurations/services/orchestrator
docker-compose up -d
```

### Configuration Docker

**Variables .env requises** :
```bash
# Tokens pour telecharger les modeles
CIVITAI_TOKEN=...
HF_TOKEN=...

# Authentification ComfyUI
COMFYUI_BEARER_TOKEN=...
COMFYUI_USERNAME=admin
COMFYUI_PASSWORD=...

# GPU
GPU_DEVICE_ID=0
CUDA_VISIBLE_DEVICES=0
```

### Volumes partages

```
docker-configurations/
├── shared/
│   ├── models/    # Cache modeles (~50GB+)
│   ├── cache/     # HuggingFace cache
│   └── outputs/   # Images generees
└── .secrets/      # Tokens (read-only)
```

## Scripts et validation

### Scripts principaux

| Script | Chemin | Usage |
|--------|--------|-------|
| `notebook_tools.py` | `scripts/` | Outil consolide : skeleton, validate, analyze, check-env |
| `notebook_helpers.py` | `scripts/` | Helpers pour manipulation notebooks et iteration |
| `extract_notebook_skeleton.py` | `scripts/` | Extraction structure pour README |
| `validate_notebooks.py` | `scripts/genai-stack/` | Validation GenAI via Papermill |
| `validate_stack.py` | `scripts/genai-stack/` | Validation ecosysteme complet |
| `check_vram.py` | `scripts/genai-stack/` | Verification VRAM disponible |
| `validate_lean_setup.py` | `MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/` | Validation environnement Lean |
| `test_notebooks.py` | `MyIA.AI.Notebooks/Probas/Infer/scripts/` | Tests Infer.NET |

**Note** : Les anciens scripts de maintenance sont archives dans `scripts/archive/`.

### Utilisation

```bash
# Outil consolide notebook_tools.py (recommande)
python scripts/notebook_tools.py skeleton MyIA.AI.Notebooks/Sudoku --output markdown
python scripts/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku --quick
python scripts/notebook_tools.py analyze MyIA.AI.Notebooks/Sudoku
python scripts/notebook_tools.py check-env Sudoku

# Helpers pour manipulation de cellules
python scripts/notebook_helpers.py list notebook.ipynb
python scripts/notebook_helpers.py analyze notebook.ipynb
python scripts/notebook_helpers.py get-source notebook.ipynb 5
python scripts/notebook_helpers.py get-output notebook.ipynb 5

# Extraction structure (alternatif)
python scripts/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku --output markdown

# Validation stack GenAI
python scripts/genai-stack/validate_stack.py

# Validation Lean
python MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/validate_lean_setup.py --wsl
```

### GitHub Actions

Le workflow `.github/workflows/notebook-validation.yml` valide automatiquement :
- Format des notebooks (JSON valide)
- Syntaxe Python/C#
- Execution de base (timeout 60s)

## Outils Claude Code

### Skills (Commandes slash)

| Commande | Description |
|----------|-------------|
| `/verify-notebooks [target]` | Verifier et tester les notebooks |
| `/enrich-notebooks [target]` | Enrichir avec du contenu pedagogique |
| `/cleanup-notebooks [target]` | Nettoyer et reorganiser le markdown |
| `/build-notebook [topic]` | Construire un nouveau notebook from scratch |
| `/execute-notebook [path]` | Executer un notebook via MCP Jupyter |
| `/validate-genai` | Valider le stack GenAI complet |

**Options** :
- `--quick` : Structure uniquement (pas d'execution)
- `--fix` : Correction automatique des erreurs
- `--python-only` / `--dotnet-only` : Filtrer par kernel
- `--consecutive` : Focus sur cellules de code consecutives
- `--iterate` : Iteration sur cellules jusqu'a objectif atteint
- `--dry-run` : Lister sans modifier

**Exemples** :
```bash
/verify-notebooks Sudoku --quick
/enrich-notebooks Infer --consecutive
/cleanup-notebooks Tweety --dry-run
```

### Agents specialises

| Agent | Fichier | Mission |
|-------|---------|---------|
| `notebook-enricher` | `.claude/agents/notebook-enricher.md` | Enrichissement pedagogique |
| `infer-notebook-enricher` | `.claude/agents/infer-notebook-enricher.md` | Specialisation Infer.NET |
| `notebook-cleaner` | `.claude/agents/notebook-cleaner.md` | Nettoyage markdown |
| `notebook-cell-iterator` | `.claude/agents/notebook-cell-iterator.md` | Iteration sur cellules |
| `readme-updater` | `.claude/agents/readme-updater.md` | Mise a jour README |
| `notebook-designer` | `.claude/agents/notebook-designer.md` | Conception de notebooks |
| `notebook-executor` | `.claude/agents/notebook-executor.md` | Execution de notebooks |
| `notebook-iterative-builder` | `.claude/agents/notebook-iterative-builder.md` | Construction iterative |
| `notebook-validator` | `.claude/agents/notebook-validator.md` | Validation de notebooks |
| `readme-hierarchy-auditor` | `.claude/agents/readme-hierarchy-auditor.md` | Audit et maintenance hierarchie README |

### MCP Jupyter Papermill

Claude Code dispose d'un MCP pour executer les notebooks :

| Categorie | Outils |
|-----------|--------|
| **Lecture/Ecriture** | `read_notebook`, `write_notebook`, `create_notebook` |
| **Cellules** | `read_cells`, `add_cell`, `update_cell`, `remove_cell` |
| **Kernels** | `list_kernels`, `manage_kernel` (start/stop/restart) |
| **Execution** | `execute_on_kernel`, `execute_notebook` |
| **Jobs async** | `manage_async_job` (status, logs, cancel) |

## Contribution

1. Fork le depot
2. Creer une branche (`git checkout -b feature/nouvelle-fonctionnalite`)
3. Commit (`git commit -m 'Add: nouvelle fonctionnalite'`)
4. Push (`git push origin feature/nouvelle-fonctionnalite`)
5. Ouvrir une Pull Request

### Conventions

- **Pas d'emojis** dans le code et les fichiers generes
- **PEP 8** pour Python, conventions standard pour C#
- **Branches** : `type/nom-court` (ex: `feature/notebook-transformers`)
- **Commits** : `Type: description` (ex: `Add: notebook sur les Transformers`)

### Structure des .env.example

Chaque famille de notebooks doit avoir un `.env.example` documentant :
- Les variables requises vs optionnelles
- Le format attendu (API key, URL, boolean)
- Les valeurs par defaut

## Licence

Ce projet est sous licence MIT - voir [LICENSE](LICENSE).

---

Repository: https://github.com/jsboige/CoursIA

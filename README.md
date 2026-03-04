# CoursIA

**Notebooks Jupyter pour l'enseignement de l'intelligence artificielle, de la theorie aux applications.**

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## Table des matieres

- [Presentation](#presentation)
- [Structure du depot](#structure-du-depot)
- [Series de notebooks](#series-de-notebooks)
- [Configuration et API Keys](#configuration-et-api-keys)
- [Kernels Jupyter](#kernels-jupyter)
- [Outils et dependances externes](#outils-et-dependances-externes)
- [Mise en route](#mise-en-route)
- [Infrastructure Docker](#infrastructure-docker)
- [Scripts et validation](#scripts-et-validation)
- [Outils Claude Code](#outils-claude-code)
- [Contribution](#contribution)

## Presentation

CoursIA est un depot de notebooks Jupyter couvrant l'ensemble du spectre de l'intelligence artificielle : algorithmes de recherche et d'optimisation, resolution de problemes par contraintes, IA symbolique et raisonnement formel, theorie des jeux, programmation probabiliste, machine learning, IA generative multimodale et trading algorithmique.

Les notebooks sont disponibles en **Python**, **C# (.NET Interactive)** et **Lean 4**. Chaque serie suit une progression pedagogique, des concepts fondamentaux vers les applications avancees. La plupart des series fonctionnent entierement en local sans configuration ; seules les series GenAI et QuantConnect necessitent des cles API.

## Structure du depot

```
CoursIA/
├── MyIA.AI.Notebooks/           # 460+ notebooks interactifs
│   ├── Search/                  # Recherche et optimisation (31 notebooks)
│   │   ├── Foundations/         # Theorie progressive
│   │   └── Applications/        # Problemes appliques (projets etudiants)
│   ├── Sudoku/                  # Resolution multi-paradigme (32 notebooks)
│   ├── SymbolicAI/              # IA Symbolique (82 notebooks)
│   │   ├── Tweety/              # Logiques formelles, argumentation (10)
│   │   ├── SemanticWeb/         # RDF, OWL, SPARQL, GraphRAG (18)
│   │   ├── Lean/                # Verification formelle Lean 4 (13)
│   │   ├── Planners/            # Planification PDDL, Fast-Downward (15)
│   │   ├── SmartContracts/      # Solidity, Move, Anchor (17)
│   │   └── Argument_Analysis/   # Analyse argumentative LLM (6)
│   ├── GameTheory/              # Theorie des jeux (26 notebooks)
│   │   ├── GameTheory-1 to 17   # Notebooks principaux (Python)
│   │   ├── *b variants          # Formalisations Lean 4
│   │   └── *c variants          # Approfondissements Python
│   ├── Probas/                  # Programmation probabiliste (22 notebooks)
│   │   ├── Infer/               # Infer.NET (20 notebooks C#)
│   │   └── Pyro_RSA_Hyperbole   # Pragmatique du langage (Python)
│   ├── ML/                      # Machine Learning (27 notebooks)
│   │   ├── ML.Net/              # Ecosysteme Microsoft (8)
│   │   └── DataScienceWithAgents/ # Data Science et agents IA (19)
│   ├── RL/                      # Reinforcement Learning (3 notebooks)
│   ├── GenAI/                   # IA Generative (97 notebooks)
│   │   ├── 00-GenAI-Environment/# Setup et configuration (6)
│   │   ├── Image/               # Generation d'images (19)
│   │   ├── Audio/               # Speech, TTS, musique (16)
│   │   ├── Video/               # Generation et comprehension (16)
│   │   ├── Texte/               # LLMs, RAG, prompt engineering (11)
│   │   ├── SemanticKernel/      # Microsoft Semantic Kernel (20)
│   │   ├── Vibe-Coding/         # Claude Code, Roo Code (5)
│   │   └── EPF/                 # Projets etudiants (4)
│   ├── QuantConnect/            # Trading algorithmique (71 notebooks)
│   │   ├── Python/              # 27 notebooks pedagogiques
│   │   ├── projects/            # 11 strategies backtestees (10 research notebooks)
│   │   └── ESGF-2026/           # Projets etudiants et exemples (34 notebooks)
│   ├── EPF/                     # Projets transversaux etudiants (4 notebooks)
│   ├── IIT/                     # Information integree - PyPhi (1)
│   └── Config/                  # Configuration API (settings.json)
│
├── scripts/                     # Scripts utilitaires
│   ├── notebook_tools.py        # CLI : validate, skeleton, analyze, check-env
│   ├── notebook_helpers.py      # Helpers pour manipulation notebooks
│   ├── extract_notebook_skeleton.py  # Extraction structure pour README
│   └── genai-stack/             # Validation GenAI (Docker, Papermill)
│
├── docker-configurations/       # Infrastructure Docker GPU
│   └── services/                # ComfyUI, FLUX, SD3.5, Z-Image
│
├── GradeBookApp/                # Systeme de notation etudiants
├── notebook-infrastructure/     # Automation Papermill et maintenance MCP
└── MyIA.AI.Shared/              # Bibliotheque C# partagee
```

---

## Series de notebooks

### Search - Recherche et Optimisation

Les algorithmes de recherche constituent le socle algorithmique de l'IA. Cette serie couvre la formalisation des espaces d'etats, les algorithmes de recherche non informee (BFS, DFS) et informee (A*, Hill Climbing), les metaheuristiques (recuit simule, algorithmes genetiques, PSO), et la programmation par contraintes (OR-Tools, Z3).

La serie est organisee en deux volets : **Foundations** (progression theorique) et **Applications** (problemes concrets : ordonnancement d'atelier, Demineur CSP, Puissance 4 avec 8 IA, detection de bords par algorithmes genetiques, optimisation de portefeuille).

31 notebooks -- Python et C# -- [README detaille](MyIA.AI.Notebooks/Search/README.md)

### Sudoku - Resolution multi-paradigme

Le meme probleme -- la resolution de grilles de Sudoku -- est aborde par une dizaine de paradigmes differents. Cela permet de comparer concretement les compromis performance/complexite/expressivite de chaque approche sur un probleme identique.

| Approche | Notebooks | Technologies |
|----------|-----------|--------------|
| Backtracking | 1 | MRV, recherche exhaustive |
| Dancing Links | 2 | Couverture exacte (DLX) |
| Metaheuristiques | 3-5 | Algorithme genetique, recuit simule, PSO |
| CSP | 6-11 | AIMA, Norvig, OR-Tools, Choco, Graph Coloring |
| Symbolique | 12-14 | Z3 SMT, Automates, BDD |
| Data-Driven | 15-18 | Infer.NET/NumPyro, reseaux de neurones, LLM |

Chaque approche dispose d'une version C# et d'une version Python (miroir).

32 notebooks -- C# et Python -- [README detaille](MyIA.AI.Notebooks/Sudoku/README.md)

**Note** : Les notebooks C# utilisent `#!import` et necessitent une execution cellule par cellule (incompatible Papermill).

### SymbolicAI - Raisonnement Formel

L'IA symbolique regroupe les systemes de raisonnement automatique. Cette serie couvre plusieurs sous-domaines complementaires :

**Tweety** (10 notebooks) -- Logiques formelles (propositionnelle, premier ordre, description) et argumentation computationnelle avec TweetyProject. Extensions de Dung, dialogues multi-agents, ASPIC+, DeLP, revision de croyances AGM.

**Semantic Web** (18 notebooks) -- Du RDF/OWL aux graphes de connaissances integres aux LLMs. Les fondations sont couvertes en .NET (dotNetRDF), puis les standards modernes en Python (SHACL, JSON-LD, RDF-Star). La serie se conclut par GraphRAG et la comparaison de raisonneurs OWL (owlrl, HermiT, reasonable, Growl).

**Lean** (13 notebooks) -- Verification formelle avec Lean 4. Types dependants, isomorphisme de Curry-Howard, tactiques Mathlib, assistance par LLMs (LeanCopilot, AlphaProof), TorchLean (reseaux de neurones formellement verifies). Necessite WSL sous Windows.

**Planners** (15 notebooks) -- Planification automatique, organisee en 4 niveaux : fondations PDDL, planification classique (Fast-Downward, heuristiques), avancee (OR-Tools scheduling, planification temporelle, HTN), et neurosymbolique (LLM-planning, Unified Planning, LOOP).

**Smart Contracts** (17 notebooks) -- De Solidity aux blockchains multi-chain (Move/Sui, Solana/Anchor). Tests avec Foundry, fuzz testing, verification formelle de smart contracts, DAO governance, account abstraction.

**Argument Analysis** (6 notebooks) -- Analyse argumentative multi-agents avec Semantic Kernel et LLMs.

| Sous-serie | Notebooks | Prerequis | README |
|------------|-----------|-----------|--------|
| Tweety | 10 | JDK 17+ (auto-telecharge) | [README](MyIA.AI.Notebooks/SymbolicAI/Tweety/README.md) |
| SemanticWeb | 18 | Python (rdflib) | [README](MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/README.md) |
| Lean | 13 | WSL, elan | [README](MyIA.AI.Notebooks/SymbolicAI/Lean/README.md) |
| Planners | 15 | Python | [README](MyIA.AI.Notebooks/SymbolicAI/Planners/README.md) |
| SmartContracts | 17 | Node.js, Foundry | [README](MyIA.AI.Notebooks/SymbolicAI/SmartContracts/README.md) |
| Argument_Analysis | 6 | OpenAI API | [README](MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/README.md) |

82 notebooks -- Python, Lean 4, C# -- [README detaille](MyIA.AI.Notebooks/SymbolicAI/README.md)

### GameTheory - Theorie des Jeux

Cette serie couvre les fondamentaux de la theorie des jeux et leurs extensions : equilibres de Nash, strategies mixtes, jeux evolutionnaires et repetes, backward induction, jeux bayesiens, CFR (Counterfactual Regret Minimization, l'algorithme a la base des IA de poker), jeux differentiels, jeux cooperatifs, mechanism design et MARL (Multi-Agent Reinforcement Learning).

L'implementation utilise Nashpy et OpenSpiel. Des side tracks en Lean 4 proposent des formalisations et preuves des theoremes classiques.

| Partie | Notebooks | Contenu |
|--------|-----------|---------|
| Fondations | 1-6 | Forme normale, Nash, minimax, jeux evolutionnaires |
| Jeux dynamiques | 7-12 | Forme extensive, backward induction, jeux bayesiens |
| Avances | 13-17 | CFR, jeux differentiels, cooperatifs, mechanism design, MARL |
| Side tracks b | 2b, 4b, 8b, 15b, 16b | Formalisations Lean 4 |
| Side tracks c | 2c, 4c, 8c, 15c, 16c | Approfondissements Python |

26 notebooks -- Python et Lean 4 -- [README detaille](MyIA.AI.Notebooks/GameTheory/README.md)

### Probas - Programmation Probabiliste

La programmation probabiliste permet de definir des modeles generatifs, propager l'incertitude et mettre a jour des croyances face a de nouvelles observations. Cette serie utilise principalement Infer.NET de Microsoft (C#) et couvre : distributions fondamentales (Gaussienne, Beta, Dirichlet), reseaux bayesiens, modeles de melange, et theorie de la decision sous incertitude.

Un notebook supplementaire explore la pragmatique du langage avec Pyro (modele RSA -- Rational Speech Acts).

| Section | Notebooks | Kernel | Contenu |
|---------|-----------|--------|---------|
| Racine | 2 | Python/C# | Infer-101 (intro), Pyro RSA (pragmatique) |
| Infer/ 1-13 | 13 | C# | Fondamentaux, modeles classiques, debugging |
| Infer/ 14-20 | 7 | C# | Theorie de la decision bayesienne |

22 notebooks -- C# (Infer.NET) et Python (Pyro) -- [README Probas](MyIA.AI.Notebooks/Probas/README.md) | [README Infer](MyIA.AI.Notebooks/Probas/Infer/README.md)

### ML - Machine Learning

Les fondamentaux de l'apprentissage automatique, organises en deux volets principaux :

**ML.Net** (8 notebooks, C#) -- Introduction a l'ecosysteme Microsoft ML.NET : features, entrainement, AutoML, evaluation.

**DataScienceWithAgents** (19 notebooks, Python) -- Parcours progressif en trois sous-series :
- *PythonForDataScience* (2 notebooks) -- NumPy et Pandas pour le pipeline Data Science.
- *PythonAgentsForDataScience* (7 notebooks, Labs 1-7) -- Construction d'agents IA pour l'analyse RFP, le screening CV, le data wrangling et la visualisation.
- *AgenticDataScience* (10 notebooks, Labs 8-17) -- Google ADK, DS-STAR et MLE-STAR pour la data science augmentee par agents, jusqu'au projet final Kaggle.

27 notebooks -- C# et Python -- [README detaille](MyIA.AI.Notebooks/ML/README.md)

### RL - Reinforcement Learning

Introduction a l'apprentissage par renforcement avec Stable Baselines3 : PPO sur CartPole, wrappers et callbacks, experience replay et DQN.

3 notebooks -- Python

### GenAI - IA Generative

La serie la plus etendue du depot, organisee par modalite. Les domaines Image, Audio et Video suivent une progression en 4 niveaux : Foundation, Advanced, Orchestration, Applications.

**Image** (19 notebooks) -- Generation et edition d'images : DALL-E 3, GPT-5, FLUX, Stable Diffusion 3.5, Qwen Image Edit. Workflows multi-modeles avec ComfyUI.

| Niveau | Contenu |
|--------|---------|
| 01-Foundation | DALL-E 3, GPT-5, Forge SD-XL Turbo, Qwen |
| 02-Advanced | Qwen Image Edit 2509, FLUX, SD 3.5, Z-Image/Lumina |
| 03-Orchestration | Comparaison multi-modeles, workflows, optimisation |
| 04-Applications | Contenu educatif, workflows creatifs, production |

**Audio** (16 notebooks) -- Synthese vocale (OpenAI TTS, Kokoro, XTTS), transcription (Whisper), generation musicale (MusicGen), separation de sources (Demucs).

| Niveau | Contenu |
|--------|---------|
| 01-Foundation | OpenAI TTS/Whisper, operations audio (librosa, pydub), Whisper local, Kokoro |
| 02-Advanced | Chatterbox TTS, XTTS voice cloning, MusicGen, Demucs |
| 03-Orchestration | Multi-model comparison, pipelines audio, temps reel (Realtime API) |
| 04-Applications | Contenu educatif, transcription pipeline, composition, sync A/V |

**Video** (16 notebooks) -- Comprehension video (GPT-5, Qwen-VL), generation (AnimateDiff, HunyuanVideo, LTX-Video, Wan, SVD), super-resolution (Real-ESRGAN).

| Niveau | Contenu |
|--------|---------|
| 01-Foundation | Operations video (moviepy, ffmpeg), GPT-5, Qwen-VL, ESRGAN, AnimateDiff |
| 02-Advanced | HunyuanVideo, LTX-Video, Wan, SVD |
| 03-Orchestration | Multi-model comparison, workflows video, ComfyUI Video |
| 04-Applications | Video educative, Sora API, workflows creatifs, production |

**Texte** (11 notebooks) -- Prompt engineering, structured outputs, RAG, reasoning, LLMs locaux, deploiement en production.

**Semantic Kernel** (20 notebooks) -- L'orchestrateur IA de Microsoft, des fondamentaux a MCP et la creation de notebooks automatisee.

**Vibe-Coding** (5 notebooks) -- Ateliers pratiques sur Claude Code et Roo Code pour le developpement assiste par IA.

| Sous-domaine | Notebooks | Services requis |
|--------------|-----------|-----------------|
| 00-Environment | 6 | - |
| Image/ | 19 | OpenAI / Docker GPU |
| Audio/ | 16 | OpenAI / GPU local |
| Video/ | 16 | OpenAI / GPU local |
| Texte/ | 11 | OpenAI API |
| SemanticKernel/ | 20 | OpenAI API |
| Vibe-Coding/ | 5 | Claude/Roo |
| EPF/ | 4 | Variable |

97 notebooks -- Python -- [README detaille](MyIA.AI.Notebooks/GenAI/README.md)

### QuantConnect - Trading Algorithmique

Application de l'IA a la finance quantitative, basee sur le framework LEAN de QuantConnect. La serie comprend trois volets :

**Notebooks pedagogiques** (27 notebooks) -- Du cycle de vie d'un algorithme LEAN aux strategies ML/DL/RL/LLM, en passant par les options, futures, risk management et analyse de sentiment.

| Phase | Notebooks | Contenu |
|-------|-----------|---------|
| Fondations LEAN | 01-04 | Setup, Platform Fundamentals, Data Management, Research |
| Universe & Assets | 05-08 | Universe Selection, Options, Futures/Forex, Multi-Asset |
| Trading Avance | 09-12 | Order Types, Risk Management, Indicators, Backtesting |
| Algorithm Framework | 13-15 | Alpha Models, Portfolio Construction, Optimization |
| Data Alternatives | 16-17 | Alternative Data, Sentiment Analysis |
| ML/DL/AI | 18-27 | Features, Classification, Regression, Deep Learning, RL, LLM |

**Strategies backtestees** (11 projets) -- Strategies completes avec notebooks de recherche standalone (yfinance/pandas). Chaque strategie est accompagnee de son code source et de ses resultats de backtest.

| Strategie | Approche | Sharpe |
|-----------|----------|--------|
| Multi-Layer-EMA | EMA multi-couches (crypto) | 1.891 |
| BTC-MACD-ADX | MACD + ADX (crypto) | 1.224 |
| OptionsIncome | Covered Call SPY + VIX filter | 0.747 |
| FuturesTrend | Donchian breakout + SPY parking | 0.588 |
| SectorMomentum | Dual Momentum SPY/TLT/GLD | 0.554 |
| TurnOfMonth | Anomalie calendaire + SPY parking | 0.536 |
| MeanReversion | RSI mean reversion + SPY parking | 0.486 |
| ForexCarry | FX momentum + SPY core-satellite | 0.476 |
| FamaFrench | Factor ETF rotation (5 facteurs) | 0.471 |
| MomentumStrategy | Rotation 11 ETFs sectoriels | 0.411 |
| AllWeather | Portfolio multi-asset (Dalio) | 0.365 |
| VIX-TermStructure | Contango SVXY + SPY parking | 0.086 |
| CryptoMultiCanal | Canaux multi-couches (crypto) | en cours |

**ESGF-2026** (34 notebooks) -- Exemples de projets etudiants et notebooks de recherche issus du cours ESGF. Inclut des exemples de strategies C# et Python avec leurs notebooks d'optimisation et d'analyse de robustesse.

71 notebooks au total -- Python -- [README detaille](MyIA.AI.Notebooks/QuantConnect/README.md) | [Projets](MyIA.AI.Notebooks/QuantConnect/projects/README.md)

### EPF - Projets Etudiants Transversaux

Notebooks de projets transversaux realises dans le cadre de cours EPF. Contenus variables selon les promotions.

4 notebooks -- Python

### IIT - Theorie de l'Information Integree

La theorie de l'information integree (Tononi) propose une approche mathematique de la conscience : un systeme est conscient dans la mesure ou il integre l'information de maniere non reducible. Ce notebook utilise PyPhi pour calculer le coefficient Phi, identifier les complexes maximaux, et explorer les concepts de cause et d'effet en information.

1 notebook -- Python -- [README detaille](MyIA.AI.Notebooks/IIT/README.md)

---

## Configuration et API Keys

La majorite des series (Search, Sudoku, ML.NET, Probas, Tweety, SemanticWeb) fonctionnent sans aucune cle API. Les series GenAI, Lean (notebooks 7-10), Argument_Analysis et QuantConnect necessitent des cles API ou des comptes sur des plateformes externes.

### Fichiers de configuration par famille

| Famille | Fichier .env | Variables cles |
|---------|--------------|----------------|
| GenAI | `MyIA.AI.Notebooks/GenAI/.env` | `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `COMFYUI_API_TOKEN` |
| Argument_Analysis | `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/.env` | `OPENAI_API_KEY`, `GLOBAL_LLM_SERVICE`, `BATCH_MODE` |
| Lean | `MyIA.AI.Notebooks/SymbolicAI/Lean/.env` | `OPENAI_API_KEY`, `GITHUB_TOKEN`, `LEAN_VERSION` |
| GameTheory | `MyIA.AI.Notebooks/GameTheory/.env` | `BATCH_MODE`, `OPENSPIEL_NUM_THREADS` |
| QuantConnect | `MyIA.AI.Notebooks/QuantConnect/.env` | `QC_USER_ID`, `QC_API_TOKEN`, `QC_ORG_ID` |
| C# Notebooks | `MyIA.AI.Notebooks/Config/settings.json` | `apikey`, `model`, `type` (openai/azure) |
| Docker ComfyUI | `docker-configurations/services/comfyui-qwen/.env` | `CIVITAI_TOKEN`, `HF_TOKEN`, `COMFYUI_BEARER_TOKEN` |

### Configuration initiale

```bash
# GenAI
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env
# Editer et ajouter: OPENAI_API_KEY, ANTHROPIC_API_KEY

# Argument Analysis
cp MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/.env.example MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/.env

# Lean (pour notebooks 7-10)
cp MyIA.AI.Notebooks/SymbolicAI/Lean/.env.example MyIA.AI.Notebooks/SymbolicAI/Lean/.env

# GameTheory
cp MyIA.AI.Notebooks/GameTheory/.env.example MyIA.AI.Notebooks/GameTheory/.env

# C# Notebooks
cp MyIA.AI.Notebooks/Config/settings.json.openai-example MyIA.AI.Notebooks/Config/settings.json

# QuantConnect
cp MyIA.AI.Notebooks/QuantConnect/.env.example MyIA.AI.Notebooks/QuantConnect/.env

# Docker ComfyUI
cp docker-configurations/services/comfyui-qwen/.env.example docker-configurations/services/comfyui-qwen/.env
```

### Variables d'environnement detaillees

**GenAI** :
```bash
OPENAI_API_KEY=sk-...
ANTHROPIC_API_KEY=sk-ant-...
OPENROUTER_API_KEY=sk-or-...          # Alternative multi-modeles
COMFYUI_API_URL=http://localhost:8188
COMFYUI_API_TOKEN=...
DEFAULT_VISION_MODEL=gpt-5-mini
GENAI_TIMEOUT_SECONDS=120
```

**Lean** :
```bash
OPENAI_API_KEY=sk-...                 # LLM Integration (notebooks 7-10)
ANTHROPIC_API_KEY=sk-ant-...
GITHUB_TOKEN=ghp_...                  # LeanDojo (notebook 10)
LEAN_VERSION=4.3.0
LEAN_TIMEOUT=30
```

---

## Kernels Jupyter

### Kernels par famille

| Famille | Kernel | Installation |
|---------|--------|--------------|
| Python notebooks | `python3` | Environnement virtuel standard |
| C# notebooks | `.net-csharp` | `dotnet tool install -g Microsoft.dotnet-interactive` |
| Lean 4 | `lean4_jupyter` | Via `elan` (WSL uniquement) |

### Installation des kernels

**Python** :
```bash
python -m venv venv
venv\Scripts\activate          # Windows
pip install jupyter ipykernel
python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"
```

**.NET Interactive** :
```bash
dotnet tool install -g Microsoft.dotnet-interactive
dotnet interactive jupyter install
```

**Lean 4** (WSL uniquement) :
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
pip install lean4_jupyter
python -m lean4_jupyter.install
```

### Limitations connues

| Probleme | Impact | Contournement |
|----------|--------|---------------|
| Papermill + `#!import` | Notebooks C# avec imports ne s'executent pas en batch | Execution cellule par cellule |
| Lean sur Windows | `signal.SIGPIPE` non supporte | Utiliser WSL |
| Cold start .NET | Premier demarrage 30-60s | Relancer apres timeout |

---

## Outils et dependances externes

### Outils principaux

| Outil | Version | Series | Installation |
|-------|---------|--------|--------------|
| Z3 SMT Solver | 4.12+ | Sudoku, SymbolicAI, Search | `pip install z3-solver` |
| OR-Tools | 9.8+ | Sudoku, Search, SymbolicAI | `pip install ortools` |
| Tweety | 1.28 | Tweety | Auto-telecharge (JARs) |
| JDK | 17+ | Tweety, Argument_Analysis | Auto-telecharge (Zulu portable) |
| PyPhi | 1.2+ | IIT | `pip install pyphi` |
| Lean 4 | 4.3+ | Lean, GameTheory | Via `elan` (WSL) |
| Mathlib4 | Latest | Lean 6+ | Auto avec `lake` |
| OpenSpiel | 1.4+ | GameTheory 13-15 | `pip install open_spiel` |
| Infer.NET | 0.4+ | Probas/Infer | Via NuGet |
| Clingo | 5.6+ | Tweety-6 | Installation manuelle |
| pySAT | 1.8+ | Tweety-2 | `pip install python-sat` |

### Outils optionnels

| Outil | Usage | Note |
|-------|-------|------|
| SPASS | Logique modale (Tweety-3) | Requiert droits admin Windows |
| EProver | FOL prover | Linux uniquement |
| MARCO | MUS enumeration | Avec Z3 |
| Fast-Downward | Planification PDDL | Auto-compilation |

---

## Mise en route

### Prerequis

- **Python 3.10+** avec pip
- **.NET 9.0 SDK** (pour notebooks C#)
- **VS Code** avec extensions Python, Jupyter, .NET Interactive
- **WSL** (pour Lean et certains outils SymbolicAI)
- **Docker + GPU** (optionnel, pour GenAI avance)

### Installation rapide

```bash
# 1. Cloner le depot
git clone https://github.com/jsboige/CoursIA.git
cd CoursIA

# 2. Environnement Python
python -m venv venv
venv\Scripts\activate          # Windows
pip install jupyter openai anthropic python-dotenv

# 3. Kernel Python
python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"

# 4. Packages .NET (si notebooks C#)
dotnet restore MyIA.CoursIA.sln

# 5. Configuration API (copier et editer selon besoins)
cp MyIA.AI.Notebooks/Config/settings.json.openai-example MyIA.AI.Notebooks/Config/settings.json
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env
```

### Installation par famille

**Sudoku / Search** (aucune config requise) :
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
```

**GameTheory** :
```bash
pip install numpy scipy matplotlib nashpy open_spiel networkx
cp MyIA.AI.Notebooks/GameTheory/.env.example MyIA.AI.Notebooks/GameTheory/.env
```

**GenAI** (Docker GPU recommande pour modeles locaux) :
```bash
pip install -r MyIA.AI.Notebooks/GenAI/requirements.txt
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env
# Editer .env avec les cles API
```

**QuantConnect** :
```bash
pip install yfinance pandas numpy matplotlib
cp MyIA.AI.Notebooks/QuantConnect/.env.example MyIA.AI.Notebooks/QuantConnect/.env
# Editer .env avec les identifiants QuantConnect
```

---

## Infrastructure Docker

Pour les notebooks GenAI avances utilisant des modeles locaux, une infrastructure Docker est fournie avec ComfyUI comme orchestrateur.

### Services disponibles

| Service | Description | VRAM requise |
|---------|-------------|--------------|
| comfyui-qwen | Qwen Image Edit 2509 (ComfyUI) | ~29 Go |
| comfyui-video | Generation video (ComfyUI) | ~12 Go |
| forge-turbo | Stable Diffusion WebUI Forge | ~10 Go |
| vllm-zimage | Z-Image / Lumina-Next-SFT | ~10 Go |
| demucs-api | Separation de sources audio | ~4 Go |
| musicgen-api | Generation musicale | ~10 Go |
| tts-api | Synthese vocale | ~2 Go |
| whisper-api | Transcription audio (API) | ~4 Go |
| whisper-webui | Transcription audio (WebUI) | ~4 Go |
| orchestrator | Gestion multi-services | - |

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
│   ├── models/    # Cache modeles (~50 Go+)
│   ├── cache/     # HuggingFace cache
│   └── outputs/   # Images generees
└── .secrets/      # Tokens (read-only)
```

---

## Scripts et validation

### Scripts principaux

| Script | Chemin | Usage |
|--------|--------|-------|
| `notebook_tools.py` | `scripts/` | CLI consolide : skeleton, validate, analyze, check-env |
| `notebook_helpers.py` | `scripts/` | Helpers pour manipulation notebooks et iteration cellules |
| `extract_notebook_skeleton.py` | `scripts/` | Extraction structure pour generation README |
| `validate_notebooks.py` | `scripts/genai-stack/` | Validation GenAI via Papermill |
| `validate_stack.py` | `scripts/genai-stack/` | Validation ecosysteme GenAI complet |
| `check_vram.py` | `scripts/genai-stack/` | Verification VRAM disponible |
| `validate_lean_setup.py` | `MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/` | Validation environnement Lean |
| `test_notebooks.py` | `MyIA.AI.Notebooks/Probas/Infer/scripts/` | Tests Infer.NET |

### Utilisation

```bash
# Outil consolide notebook_tools.py
python scripts/notebook_tools.py skeleton MyIA.AI.Notebooks/Sudoku --output markdown
python scripts/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku --quick
python scripts/notebook_tools.py analyze MyIA.AI.Notebooks/Sudoku
python scripts/notebook_tools.py check-env Sudoku

# Helpers pour manipulation de cellules
python scripts/notebook_helpers.py list notebook.ipynb
python scripts/notebook_helpers.py analyze notebook.ipynb
python scripts/notebook_helpers.py get-source notebook.ipynb 5

# Validation stack GenAI
python scripts/genai-stack/genai.py validate --full

# Validation Lean
python MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/validate_lean_setup.py --wsl
```

### GitHub Actions

Le workflow `.github/workflows/notebook-validation.yml` valide automatiquement a chaque pull request :
- Format des notebooks (JSON valide)
- Syntaxe Python/C#
- Execution de base (timeout 60s)

---

## Outils Claude Code

Ce depot inclut une configuration pour Claude Code avec des agents specialises et des commandes slash pour la maintenance des notebooks.

### Commandes slash

| Commande | Description |
|----------|-------------|
| `/verify-notebooks [target]` | Verifier et tester les notebooks |
| `/enrich-notebooks [target]` | Enrichir avec du contenu pedagogique |
| `/cleanup-notebooks [target]` | Nettoyer et reorganiser le markdown |
| `/build-notebook [topic]` | Construire un nouveau notebook |
| `/execute-notebook [path]` | Executer un notebook via MCP Jupyter |
| `/validate-genai` | Valider le stack GenAI complet |
| `/qc-iterative-improve [strategy]` | Amelioration iterative de strategies QC |

Options : `--quick`, `--fix`, `--python-only`, `--dotnet-only`, `--consecutive`, `--dry-run`

### Agents specialises

| Agent | Mission |
|-------|---------|
| notebook-enricher | Enrichissement pedagogique |
| infer-notebook-enricher | Specialisation Infer.NET |
| notebook-cleaner | Nettoyage markdown |
| notebook-cell-iterator | Iteration sur cellules |
| notebook-designer | Conception de notebooks |
| notebook-executor | Execution de notebooks |
| notebook-iterative-builder | Construction iterative |
| notebook-validator | Validation de notebooks |
| notebook-modernizer | Modernisation bibliotheques |
| qc-strategy-analyzer | Analyse backtests QuantConnect |
| qc-strategy-improver | Amelioration iterative strategies |
| qc-robustness-researcher | Recherche robustesse strategies |
| qc-research-notebook | Notebooks de recherche QC |
| readme-updater | Mise a jour README |
| readme-hierarchy-auditor | Audit hierarchie README |

Configuration dans `.claude/agents/` et `.claude/skills/`.

---

## Contribution

1. Fork le depot
2. Creer une branche (`git checkout -b feature/nouveau-notebook`)
3. Commit (`git commit -m 'Add: notebook sur les Transformers'`)
4. Push et ouvrir une Pull Request

Conventions : PEP 8 pour Python, conventions standard pour C#, pas d'emojis dans le code, documentation en francais. Chaque famille de notebooks doit inclure un `.env.example` documentant les variables requises.

## Licence

Ce projet est sous licence MIT - voir [LICENSE](LICENSE).

---

Repository : https://github.com/jsboige/CoursIA

# CoursIA

**Une plateforme educative complete pour maitriser l'intelligence artificielle, de la theorie a la pratique.**

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## Table des matieres

- [Introduction](#introduction)
- [Philosophie pedagogique](#philosophie-pedagogique)
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

Bienvenue dans **CoursIA**, un depot de **290+ notebooks Jupyter** concus pour vous guider dans l'apprentissage de l'intelligence artificielle. Cette plateforme couvre l'ensemble du spectre de l'IA moderne : des algorithmes classiques de recherche et d'optimisation jusqu'aux techniques les plus avancees de l'IA generative.

**Ce que vous trouverez ici :**

- **Recherche & Optimisation** : Les fondements algorithmiques - de la recherche aveugle (BFS, DFS) aux metaheuristiques (recuit simule, algorithmes genetiques), en passant par la programmation par contraintes avec OR-Tools et Z3.

- **Resolution de Sudoku** : Un cas d'etude unique ou le meme probleme est attaque sous tous les angles imaginables - backtracking, algorithmes genetiques, CSP, solveurs SMT, et meme une approche probabiliste bayesienne.

- **IA Symbolique** : L'art du raisonnement automatique, des syllogismes d'Aristote aux assistants de preuves modernes. Explorez les logiques formelles, l'argumentation computationnelle avec TweetyProject, le Web Semantique (RDF, OWL, SPARQL), et la verification formelle avec Lean 4.

- **Theorie des Jeux** : Comprendre l'interaction strategique - equilibres de Nash, jeux evolutionnaires, jeux cooperatifs, et les algorithmes revolutionnaires comme CFR qui ont permis aux IA de dominer le poker.

- **Probabilites** : Maitriser l'incertitude avec la programmation probabiliste. Infer.NET de Microsoft vous permettra de definir des modeles bayesiens et de propager les croyances face a de nouvelles observations.

- **Machine Learning** : Les fondamentaux de l'apprentissage automatique avec ML.NET pour l'ecosysteme .NET, et Python pour les pipelines Data Science modernes incluant le Reinforcement Learning.

- **IA Generative** : L'ere des modeles generatifs - generation d'images (DALL-E 3, FLUX, Stable Diffusion, Qwen), synthese vocale et musicale (Whisper, MusicGen, Demucs), comprehension et generation video (GPT-5 Vision, AnimateDiff, HunyuanVideo).

- **Trading Algorithmique** : Application concrete de l'IA a la finance avec QuantConnect LEAN. Du backtesting basique aux strategies ML/DL/RL en passant par l'analyse de sentiment par LLM.

Les notebooks sont disponibles en **C# (.NET Interactive)**, **Python** et **Lean 4**, avec une documentation pedagogique progressive permettant aussi bien l'autoformation que l'enseignement encadre.

## Philosophie pedagogique

CoursIA n'est pas un simple catalogue de tutoriels. Chaque serie est concue selon une **progression pedagogique rigoureuse** :

1. **Comprendre avant d'appliquer** : Les concepts theoriques sont introduces avec des exemples simples avant de passer a l'implementation.

2. **Pratiquer en autonomy** : Chaque notebook contient des exercices avec corrections, permettant de valider ses connaissances au fur et a mesure.

3. **Comparer les approches** : La serie Sudoku illustre parfaitement cette philosophie - un seul probleme resolu par une dizaine de paradigmes differents, permettant de comprendre les compromis performance/complexite/expressivite.

4. **Du local vers le cloud** : Les notebooks sont concus pour fonctionner localement, mais s'integrent aussi avec des services cloud (QuantConnect, OpenAI API, Docker GPU) pour les cas avances.

5. **Bilingualisme technique** : La plupart des series proposent des equivalents C# et Python, refletant la realite du marche ou ces deux ecosystemes coexistent.

**Temps d'etude estime** : L'ensemble du contenu represente environ **185 heures** d'apprentissage, soit l'equivalent d'un cursus universitaire complet en IA.

## Cartographie complete

### Structure du depot

```
CoursIA/
├── MyIA.AI.Notebooks/           # 301+ notebooks interactifs
│   ├── Search/                  # Recherche et optimisation (31 notebooks)
│   │   ├── Foundations/         # 12 notebooks theoriques
│   │   └── Applications/        # 14 notebooks projets etudiants
│   ├── Sudoku/                  # Resolution Sudoku (31 notebooks)
│   ├── SymbolicAI/              # IA Symbolique (47 notebooks)
│   │   ├── Tweety/              # TweetyProject - 10 notebooks
│   │   ├── SemanticWeb/         # RDF, OWL, SPARQL, reasoners (18 notebooks)
│   │   ├── Lean/                # Lean 4 - 10 notebooks
│   │   ├── Argument_Analysis/   # Analyse argumentative - 6 notebooks
│   │   └── Planners/            # Fast-Downward, PDDL
│   │
│   ├── GameTheory/              # Theorie des jeux (26 notebooks)
│   │   ├── GameTheory-1 to 17   # Notebooks principaux
│   │   └── *b, *c variants      # Lean + Python side tracks
│   │
│   ├── Probas/Infer/            # Infer.NET - 20 notebooks
│   ├── Probas/                  # Probabilites - racine (2 notebooks)
│   ├── ML/                      # Machine Learning (17 notebooks)
│   │   ├── RL/                  # Reinforcement Learning (3 notebooks)
│   │   └── *                    # ML.NET, Python Data Science (14 notebooks)
│   │
│   ├── GenAI/                   # IA Generative (96 notebooks)
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
│   │   ├── SemanticKernel/      # Microsoft Semantic Kernel (20 notebooks)
│   │   ├── EPF/                 # Projets etudiants (4 notebooks)
│   │   └── Vibe-Coding/         # Claude Code et Roo Code tutorials (5 notebooks)
│   │
│   ├── QuantConnect/            # Trading algorithmique + AI (27 notebooks Python)
│   ├── IIT/                     # PyPhi - Information integree (1 notebook)
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
├── GradeBookApp/                # Systeme de notation etudiants (grading collegial)
├── notebook-infrastructure/     # Automation Papermill et maintenance MCP Jupyter
└── MyIA.AI.Shared/              # Bibliotheque C# partagee pour notebooks .NET
```

### Statistiques globales

| Categorie | Notebooks | Kernels | Duree estimee | API requise |
|-----------|-----------|---------|---------------|-------------|
| **Search** | 31 | Python, C# | ~22h | - |
| **Sudoku** | 31 | C#, Python | ~8h | - |
| **SymbolicAI** | 47 | Python, Lean 4 | ~32h | OpenAI (optionnel) |
| **GameTheory** | 26 | Python, Lean 4 | ~18h30 | OpenAI (optionnel) |
| **Probas** | 22 | C#, Python | ~17h | - |
| **ML** | 17 | C#, Python | ~6h | - |
| **RL** | 3 | Python | ~2h | - |
| **GenAI** | 96 | Python | ~65h | OpenAI/Anthropic |
| **QuantConnect** | 27 | Python | ~30h | QuantConnect (gratuit) |
| **IIT** | 1 | Python | ~1h30 | - |
| **Total** | **301+** | **Mixed** | **~203h** | - |

## Series de notebooks

### Search - Recherche et Optimisation

Les algorithmes de recherche constituent le socle fondamental de l'intelligence artificielle. Cette serie de **31 notebooks** vous guide de la formalisation des espaces d'etats jusqu'aux metaheuristiques les plus avancees, avec une organisation claire en deux volets complementaires.

**Organisation en deux volets** :

- **Foundations/** (12 notebooks) : Progression theorique rigoureuse, des espaces d'etats (Search-1) aux automates symboliques (Search-12), en couvrant la recherche non informee (BFS, DFS), informee (A*), les algorithmes genetiques, la programmation par contraintes (CSP), les metaheuristiques (PSO, ABC, SA), le Dancing Links, et la programmation lineaire.

- **Applications/** (14 notebooks) : Problemes du monde reel adaptes de projets etudiants EPITA, EPF et ECE. Planification d'infirmiers, ordonnancement d'atelier, resolution de Wordle, Demineur CSP, Picross, Puissance 4 avec 8 algorithmes IA differents.

**Ce que vous apprendrez** : Formaliser un probleme comme espace d'etats, choisir l'algorithme adapte (complet vs optimal vs efficace), implementer des contraintes avec OR-Tools, comparer metaheuristiques sur des benchmarks, et appliquer ces techniques a des problemes industriels reels.

**31 notebooks** organises en Foundations (12) et Applications (14), plus 5 notebooks legacies.

| Volet | Notebooks | Contenu |
|-------|-----------|---------|
| **Foundations** | 12 | StateSpace, Uninformed, Informed, LocalSearch, GA, CSP (3), Metaheuristics, DLX, LP, Automata |
| **Applications** | 14 | NQueens, GraphColoring, NurseScheduling, JobShop, Timetabling, Minesweeper, Wordle, MiniZinc, EdgeDetection, Portfolio, Picross, ConnectFour |
| **Legacy** | 5 | CSPs_Intro, Exploration, GeneticSharp, Portfolio, PyGAD |

[README Search](MyIA.AI.Notebooks/Search/README.md)

### Sudoku - Resolution par Contraintes

Une approche comparative des algorithmes de resolution. Ce qui rend cette serie unique : le meme probleme resolu avec de nombreuses techniques differentes ! Vous comparerez le backtracking naif, les algorithmes genetiques, la programmation par contraintes (OR-Tools), les solveurs SMT (Z3), et meme une approche probabiliste (Infer.NET). Ideal pour comprendre les compromis performance/complexite de chaque paradigme.

**31 notebooks** (16 C#, 15 Python) illustrant differentes approches algorithmiques avec miroir C#/Python.

| Approche | Notebooks | Technologies | Kernel |
|----------|-----------|--------------|--------|
| **Backtracking** | 1 | MRV, recherche exhaustive | C#, Python |
| **Dancing Links** | 2 | Couverture exacte (DLX) | C#, Python |
| **Metaheuristiques** | 3-5 | Genetique, Recuit simule, PSO | C#, Python |
| **CSP** | 6-11 | AIMA, Norvig, OR-Tools, Choco, Graph Coloring | C#, Python |
| **Symbolique** | 12-14 | Z3 SMT, Automates, BDD | C# |
| **Data-Driven** | 15-18 | Infer.NET/NumPyro, Neural Network, LLM | C#, Python |

**Note** : Les notebooks C# utilisent `#!import` et necessitent une execution cellule par cellule (Papermill incompatible).

[README Sudoku](MyIA.AI.Notebooks/Sudoku/README.md)

### SymbolicAI - IA Symbolique

Decouverte des logiques formelles et de l'argumentation computationnelle. Cette serie vous fera explorer les systemes de raisonnement automatique, de la logique propositionnelle aux frameworks d'argumentation de Dung, en passant par la verification de theoremes avec Lean 4. Vous apprendrez a utiliser **TweetyProject** (bibliotheque Java via JPype) pour manipuler des bases de connaissances, calculer des extensions d'argumentation, et modeliser des dialogues multi-agents. La serie couvre egalement les extensions avancees (ASPIC+, DeLP, ADF), la revision de croyances AGM, et les systemes de preferences.

**47 notebooks** couvrant les logiques formelles, l'argumentation computationnelle, le Web Semantique et la verification formelle.

| Serie | Notebooks | Contenu | Prerequis | README |
|-------|-----------|---------|-----------|--------|
| **Tweety** | 10 | TweetyProject, logiques PL/FOL/DL, argumentation Dung, ASPIC+ | JDK 17+ (auto) | [README](MyIA.AI.Notebooks/SymbolicAI/Tweety/README.md) |
| **SemanticWeb** | 18 | RDF, OWL, SPARQL, reasoners, SHACL, GraphRAG | Python (rdflib) | [README](MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/README.md) |
| **Lean** | 10 | Lean 4, types dependants, tactiques, Mathlib, LLM integration | WSL, elan | [README](MyIA.AI.Notebooks/SymbolicAI/Lean/README.md) |
| **Argument_Analysis** | 6 | Analyse argumentative multi-agents avec Semantic Kernel | OpenAI API | [README](MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/README.md) |
| **Planners** | 1 | Fast-Downward, planification PDDL | Python | [README](MyIA.AI.Notebooks/SymbolicAI/Planners/README.md) |
| **Autres** | 14+ | Z3, OR-Tools, RDF.NET | Varies | - |

**Focus sur Lean 4** : Cette sous-serie vous initie a la verification formelle avec Lean 4, un assistant de preuves et langage de programmation fonctionnel base sur la theorie des types dependants. Vous progresserez des fondements (types dependants, isomorphisme de Curry-Howard) jusqu'aux tactiques avancees de Mathlib, puis decouvrirez l'etat de l'art de l'assistance par LLMs (LeanCopilot, AlphaProof) et les agents autonomes pour la preuve mathematique. Note : necessite WSL sous Windows.

**Focus sur Semantic Web** : Cette serie de 14 notebooks couvre l'ensemble du spectre du Web Semantique, des fondations RDF aux graphes de connaissances integres aux LLMs. Vous commencerez avec .NET et dotNetRDF pour apprehender les concepts fondamentaux (triples, graphes, SPARQL), puis transitionnerez vers Python pour les standards modernes (SHACL pour la validation de donnees, JSON-LD pour le SEO, RDF-Star pour les annotations). La serie se termine par une connexion moderne avec l'IA : construction de graphes de connaissances (kglab, OWLReady2), GraphRAG (combinaison KG + LLMs), et comparaison de raisonneurs OWL (owlrl, HermiT, reasonable, Growl).

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

### ML - Machine Learning

**17 notebooks** couvrant ML.NET (C#), Python Data Science et Reinforcement Learning.

| Section | Notebooks | Contenu |
|---------|-----------|---------|
| **ML.NET** | 5 | Introduction, Features, Entrainement, AutoML, Evaluation |
| **Python Foundations** | 2 | NumPy, Pandas |
| **AI Agents Workshop** | 7 | RFP Analysis, CV Screening, Data Wrangling, First Agent |
| **Reinforcement Learning** | 3 | Stable Baselines3, PPO, SAC/DDPG, HER |

[README ML](MyIA.AI.Notebooks/ML/README.md)

### GenAI - IA Generative

L'ere des modeles generatifs a profondement transforme le paysage de l'intelligence artificielle. Cette serie de **96 notebooks** vous guide des premiers pas avec l'API OpenAI jusqu'a la maitrise de workflows multi-modaux complexes.

**Ce que vous apprendrez :**

- **Generation d'images** : Maitrisez l'art de la creation visuelle avec DALL-E 3 pour la generation rapide, FLUX pour la qualite artistique, Stable Diffusion 3.5 pour le controle fin, et Qwen Image Edit pour l'edition intelligente. Vous decouvrirez egalement l'architecture ComfyUI pour l'orchestration de workflows GPU.

- **Synthese audio** : De la synthese vocale (OpenAI TTS, Kokoro) au clonage de voix (XTTS), en passant par la generation musicale (MusicGen) et la separation de sources (Demucs). Creez des experiences audio immersives et professionnelles.

- **Generation video** : Explorez les frontieres de la creation video avec AnimateDiff pour l'animation, HunyuanVideo et LTX-Video pour la generation text-to-video, et la comprehension video avec GPT-5 Vision et Qwen2.5-VL.

- **LLMs et orchestration** : Maitrisez le prompt engineering, les outputs structures, le RAG (Retrieval-Augmented Generation), et l'integration avec Microsoft Semantic Kernel pour construire des agents intelligents.

**Organisation pedagogique** : Chaque domaine (Image, Audio, Video, Texte) suit une progression en 4 niveaux - Foundation, Advanced, Orchestration, Applications - permettant une montee en competence progressive.

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

### QuantConnect - Trading Algorithmique + AI

Le trading algorithmique represente l'une des applications les plus concretes de l'IA en entreprise. Cette serie de **27 notebooks** vous initie au framework LEAN de QuantConnect, de la conception de strategies basiques jusqu'a l'integration de modeles de machine learning et de LLMs pour l'analyse de sentiment.

**Pourquoi QuantConnect ?** La plateforme offre un acces gratuit a des donnees de marche de qualite institutionnelle, un moteur de backtesting robuste, et la possibilite de deployer des strategies en production. C'est l'environnement ideal pour apprendre le trading algorithmique sans investissement en infrastructure.

**Parcours pedagogique** :

1. **Fondations** : Maitrisez le cycle de vie d'un algorithme, la gestion des donnees historiques, et le workflow de recherche avec QuantBook.

2. **Classes d'actifs** : Explorez les specificites des actions, options, futures et forex. Apprenez a selectionner dynamiquement des univers de titres.

3. **Risk Management** : Implementez des strategies de gestion du risque professionnelles - position sizing, stop-loss, portfolio heat.

4. **Machine Learning** : Integrez des modeles de classification et regression pour la prediction de mouvements, du deep learning pour la reconnaissance de patterns, et du reinforcement learning pour l'optimisation de strategies.

5. **LLM Integration** : Utilisez les LLMs pour l'analyse de sentiment a partir de news et reseaux sociaux, ouvrant la voie aux strategies basees sur l'actualite.

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

### IIT - Integrated Information Theory

La theorie de l'information integree, developpee par Giulio Tononi, propose une approche mathematique originale de la conscience. Selon cette theorie, un systeme est conscient dans la mesure ou il integre l'information de maniere non reducible - c'est-a-dire que le tout contient plus d'information que la somme de ses parties.

Ce notebook vous initie a **PyPhi**, la bibliotheque de reference pour calculer les mesures de l'IIT. Vous apprendrez a construire des matrices de transition (TPM), calculer le coefficient Phi d'un systeme, identifier les complexes maximaux, et comprendre les concepts de cause et d'effet en information.

**1 notebook** sur PyPhi et la theorie de l'information integree.

| Notebook | Contenu | Duree |
|----------|---------|-------|
| [Intro_to_PyPhi](MyIA.AI.Notebooks/IIT/Intro_to_PyPhi.ipynb) | TPM, Phi, CES, Causation actuelle, Macro-subsystemes | ~90 min |

[README IIT](MyIA.AI.Notebooks/IIT/README.md)

## Configuration et API Keys

La plateforme CoursIA s'articule autour de deux types d'environnements : les notebooks autonomes (sans configuration requise) et les notebooks connectes (necessitant des cles API ou des services externes). Cette section vous guide dans la configuration de votre environnement en fonction des series que vous souhaitez explorer.

**Configuration minimale** : Les series Search, Sudoku, ML.NET, Probas et SymbolicAI (Tweety, SemanticWeb) fonctionnent entierement en local sans aucune cle API.

**Configuration etendue** : Les series GenAI, Lean (notebooks 7-10), Argument_Analysis et QuantConnect necessitent des cles API ou des comptes sur des plateformes externes.

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

Pour les utilisateurs souhaitant explorer les capacites avancees de generation d'images et de video, CoursIA fournit une infrastructure Docker complete. Cette architecture permet de faire tourner localement des modeles generatifs de pointe sans dependre exclusivement des APIs cloud.

**Pourquoi Docker ?** Les modeles de generation d'images comme Qwen Image Edit ou FLUX necessitent des ressources GPU substantielles (10-30 Go de VRAM). L'approche conteneurisee permet d'isoler les dependances, de partager les modeles entre services, et de reproduire un environnement de production complet.

**Architecture** : L'infrastructure s'appuie sur ComfyUI comme orchestrateur principal, avec des nodes customises pour Qwen, FLUX et Stable Diffusion. Un service orchestrator permet de basculer entre differents modeles selon les besoins.

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

La qualite et la maintenabilite d'un depot de 290+ notebooks reposent sur une infrastructure de validation robuste. Cette section presente les outils developpes pour assurer la coherence du contenu et faciliter la contribution.

**Philosophie de validation** : Chaque notebook est valide automatiquement par GitHub Actions a chaque pull request. Les verifications incluent le format JSON, la syntaxe du code, et l'execution de base. Cette approche garantit que le depot reste dans un etat fonctionnel tout au long de son evolution.

**Outils a disposition** : Les scripts `notebook_tools.py` et `notebook_helpers.py` fournissent une interface unifiee pour manipuler, analyser et valider les notebooks. Ils sont utilises en interne par les agents Claude Code pour l'enrichissement et la maintenance.

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

Ce depot est optimise pour une utilisation avec **Claude Code**, l'assistant de programmation d'Anthropic. Une infrastructure complete d'agents specialises et de commandes slash a ete developpee pour faciliter la creation, l'enrichissement et la maintenance des notebooks.

**Pourquoi cette integration ?** La maintenance de 290+ notebooks represente un defi considerable. Les agents Claude Code automatisent les taches repetitives - verification de syntaxe, ajout de contenu pedagogique, nettoyage markdown - tout en garantissant une qualite homogene.

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

## Parcours recommandes

Selon votre profil et vos objectifs, voici quelques suggestions de parcours a travers le depot :

**Debutant en IA** : Commencez par ML (ML.NET et Python Data Science) pour comprendre les fondamentaux de l'apprentissage automatique. Poursuivez avec Search pour les algorithmes classiques, puis Probas pour l'inference bayesienne. Terminez par une introduction a GenAI pour decouvrir les LLMs.

**Developpeur C#/.NET** : Les series ML.NET, Probas (Infer.NET) et Sudoku vous offriront une experience complete dans l'ecosysteme Microsoft. La serie Sudoku est particulierement adaptee pour comparer differentes approches algorithmiques.

**Data Scientist Python** : Les series GenAI, QuantConnect et ML (Python Data Science) constituent un parcours coherent. Ajoutez GameTheory pour une perspective strategique et RL pour le reinforcement learning.

**Chercheur en IA symbolique** : Les series SymbolicAI (Tweety, Lean, SemanticWeb) et GameTheory offrent une plongee dans le raisonnement formel, l'argumentation et la verification de preuves.

**Curieux de GenAI** : La serie GenAI est auto-suffisante et peut etre suivie independamment. Commencez par Texte pour maitriser les LLMs, puis explorez Image, Audio et Video selon vos interets.

## Licence

Ce projet est sous licence MIT - voir [LICENSE](LICENSE).

---

Repository: https://github.com/jsboige/CoursIA

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

Ce depot contient **180+ notebooks Jupyter** interactifs couvrant :
- **IA Symbolique** : Logiques formelles, argumentation, verification formelle (Lean 4, Tweety, Z3)
- **Probabilites** : Inference bayesienne, modeles graphiques (Infer.NET)
- **Theorie des jeux** : Nash, jeux evolutionnaires, cooperatifs, CFR, OpenSpiel
- **Machine Learning** : ML.NET, algorithmes genetiques
- **IA Generative** : OpenAI, LLMs, generation d'images (DALL-E, FLUX, Qwen, SD3.5)

Les notebooks sont en **C# (.NET Interactive)**, **Python** et **Lean 4**, avec une documentation pedagogique complete.

## Cartographie complete

### Structure du depot

```
CoursIA/
├── MyIA.AI.Notebooks/           # 180+ notebooks interactifs
│   ├── GenAI/                   # IA Generative (18 notebooks)
│   │   ├── 00-Environment/      # Setup et configuration
│   │   ├── 01-Foundation/       # DALL-E 3, GPT-5
│   │   ├── 02-Advanced/         # Qwen, FLUX, SD3.5, Z-Image
│   │   ├── 03-Orchestration/    # Multi-modeles, workflows
│   │   └── 04-Applications/     # Production, contenu educatif
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
│   ├── ML/                      # Machine Learning (5+ notebooks)
│   ├── IIT/                     # PyPhi - Information integree (3 notebooks)
│   ├── EPF/                     # Devoirs etudiants (15+ notebooks)
│   └── Config/                  # Configuration API (settings.json)
│
├── .claude/                     # Configuration Claude Code
│   ├── agents/                  # 4 agents specialises
│   └── commands/                # 3 skills (commandes slash)
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
| **GenAI** | 18 | Python | ~6h | OpenAI/Anthropic |
| **Sudoku** | 11 | C#, Python | ~2h | - |
| **Search** | 5 | C#, Python | ~1h10 | - |
| **ML** | 5+ | C# | ~1h30 | - |
| **IIT** | 3 | Python | ~1h | - |
| **Total** | **180+** | **Mixed** | **~75h** | - |

## Series de notebooks

### SymbolicAI - IA Symbolique

**47+ notebooks** couvrant les logiques formelles, l'argumentation computationnelle et la verification formelle.

| Serie | Notebooks | Contenu | Prerequis | README |
|-------|-----------|---------|-----------|--------|
| **Tweety** | 10 | TweetyProject, logiques PL/FOL/DL, argumentation Dung, ASPIC+ | JDK 17+ (auto) | [README](MyIA.AI.Notebooks/SymbolicAI/Tweety/README.md) |
| **Lean** | 10 | Lean 4, types dependants, tactiques, Mathlib, LLM integration | WSL, elan | [README](MyIA.AI.Notebooks/SymbolicAI/Lean/README.md) |
| **Argument_Analysis** | 6 | Analyse argumentative multi-agents avec Semantic Kernel | OpenAI API | - |
| **Autres** | 21+ | Z3, OR-Tools, RDF.NET, Fast-Downward | Varies | - |

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

**26 notebooks** (17 principaux + 9 side tracks) combinant Python et Lean 4.

| Partie | Notebooks | Contenu | Kernel |
|--------|-----------|---------|--------|
| **Fondations** | 1-6 | Forme normale, Nash, minimax, jeux evolutionnaires | Python |
| **Jeux dynamiques** | 7-12 | Forme extensive, backward induction, jeux bayesiens | Python |
| **Avances** | 13-17 | CFR, jeux differentiels, cooperatifs, mechanism design, MARL | Python + OpenSpiel |
| **Side tracks b** | 2b, 4b, 8b, 15b, 16b | Formalisations Lean 4 | Lean 4 (WSL) |
| **Side tracks c** | 2c, 4c, 8c, 15c, 16c | Approfondissements Python | Python |

[README GameTheory](MyIA.AI.Notebooks/GameTheory/README.md)

### Probas/Infer - Programmation Probabiliste

**20 notebooks** sur Infer.NET couvrant l'inference bayesienne et la theorie de la decision.

| Groupe | Notebooks | Contenu | Duree |
|--------|-----------|---------|-------|
| **Fondamentaux** | 1-3 | Setup, Gaussiennes, Factor Graphs | ~2h |
| **Modeles classiques** | 4-6 | Reseaux bayesiens, IRT/DINA, TrueSkill | ~3h |
| **Classification** | 7-8 | Probit/BPM, selection de modeles | ~2h |
| **Avances** | 9-12 | LDA, crowdsourcing, HMM, recommandation | ~4h |
| **Reference** | 13 | Debugging, bonnes pratiques | ~1h |
| **Decision** | 14-20 | Theorie de la decision, utilite, VOI, POMDP | ~5h |

[README Infer](MyIA.AI.Notebooks/Probas/Infer/README.md)

### Sudoku - Resolution par Contraintes

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

**18 notebooks** organises en 4 niveaux progressifs.

| Niveau | Contenu | Services requis |
|--------|---------|-----------------|
| **00-Environment** | Setup, Docker, API configuration | - |
| **01-Foundation** | DALL-E 3, GPT-5, operations de base | OpenAI API |
| **02-Advanced** | Qwen Image Edit, FLUX, Stable Diffusion 3.5, Z-Image | Docker GPU |
| **03-Orchestration** | Comparaison multi-modeles, workflows | Docker GPU |
| **04-Applications** | Contenu educatif, integration production | OpenAI/Docker |

[README GenAI](MyIA.AI.Notebooks/GenAI/README.md)

### IIT - Integrated Information Theory

**3 notebooks** sur PyPhi et la theorie de l'information integree.

| Notebook | Contenu |
|----------|---------|
| Intro_to_PyPhi | Introduction, concepts de base |
| IIT_Networks | Reseaux et phi |
| IIT_Analysis | Analyse avancee |

### ML - Machine Learning

**5+ notebooks** sur ML.NET et AutoML.

- ML-1 a ML-4 : Introduction, Features, Entrainement, Evaluation
- TP-prevision-ventes : Projet pratique

## Configuration et API Keys

### Fichiers de configuration par famille

| Famille | Fichier .env | Variables cles |
|---------|--------------|----------------|
| **GenAI** | `MyIA.AI.Notebooks/GenAI/.env` | `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `COMFYUI_API_TOKEN` |
| **Argument_Analysis** | `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/.env` | `OPENAI_API_KEY`, `GLOBAL_LLM_SERVICE`, `BATCH_MODE` |
| **Lean** | `MyIA.AI.Notebooks/SymbolicAI/Lean/.env` | `OPENAI_API_KEY`, `GITHUB_TOKEN`, `LEAN_VERSION` |
| **GameTheory** | `MyIA.AI.Notebooks/GameTheory/.env` | `BATCH_MODE`, `OPENSPIEL_NUM_THREADS` |
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

1. **ML** - Introduction au Machine Learning avec ML.NET
2. **Sudoku** - Algorithmes de resolution (backtracking, contraintes)
3. **Search** - Recherche et optimisation
4. **SymbolicAI/Tweety** - Logiques formelles et argumentation
5. **Probas/Infer** - Inference bayesienne
6. **GameTheory** - Theorie des jeux
7. **SymbolicAI/Lean** - Verification formelle (WSL requis)
8. **GenAI** - IA generative (API keys requises)

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

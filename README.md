# CoursIA

**Apprendre l'intelligence artificielle par la pratique, des fondements theoriques aux applications avancees.**

CoursIA est une collection de notebooks Jupyter interactifs couvrant l'ensemble du spectre de l'IA : algorithmes de recherche, resolution par contraintes, raisonnement formel, theorie des jeux, programmation probabiliste, machine learning, IA generative multimodale et trading algorithmique.

Les notebooks sont disponibles en Python, C# (.NET Interactive) et Lean 4. Chaque serie suit une progression pedagogique, des concepts fondamentaux vers les applications avancees. La plupart fonctionnent en local sans configuration ; seules les series GenAI et QuantConnect necessitent des cles API.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

---

## Parcours recommandes

**Debutant** -- Commencer par Search (Part 1), Sudoku, puis ML.Net. Ces series ne necessitent aucune cle API et introduisent les concepts fondamentaux.

**Intermediaire** -- Explorer GameTheory, Probas, puis la partie Foundations de GenAI (Image, Texte). Ajoutez les techniques probabilistes et generatives a votre boite a outils.

**Avance** -- SymbolicAI (Lean, SmartContracts), QuantConnect (strategies ML/DL), GenAI Video/Audio. Pour les etudiants a l'aise avec les fondamentaux qui veulent aller plus loin.

**Recherche** -- ML Training Pipeline (forecasting, GNN), SymbolicAI (preuves formelles Lean 4), Infer.NET (programmation probabiliste avancee).

---

## Ce qu'on y trouve

Le depot couvre un spectre inhabituellement large de l'IA, des algorithmes classiques aux modeles generatifs les plus recents. Quelques points remarquables :

- **Multi-langages** : Python pour le ML et l'IA generative, C# pour l'ecosysteme Microsoft (ML.NET, Infer.NET, Semantic Kernel), Lean 4 pour la verification formelle
- **Donnees reelles** : les notebooks QuantConnect utilisent des donnees de marche reelles via yfinance ; le ML Training Pipeline travaille sur un panier de 10 cryptomonnaies avec validation walk-forward stricte
- **Infrastructure complete** : les notebooks GenAI peuvent utiliser des modeles locaux via Docker (Qwen, FLUX, ComfyUI) ou des APIs cloud (OpenAI, Anthropic)
- **Preuves formelles** : les series Lean et GameTheory proposent des preuves mecanisees en Lean 4, un aspect rare dans les cours d'IA

---

## Philosophie pedagogique

Chaque serie est concue pour etre **self-contained** : un etudiant peut ouvrir n'importe quel notebook et suivre la progression sans prerequis externes, les explications etant integrees au fil des cellules.

Les approches **multi-paradigmes** sont privilegiees : le Sudoku est resolu par backtracking, CSP, metaheuristiques et reseaux de neurones pour comparer les compromis. Les jeux sont formalises en Python et en Lean 4. Cette diversite d'approches sur un meme probleme est au coeur de la demarche.

Les notebooks combinent **theorie et implementation** : les concepts sont introduits progressivement, puis mis en pratique dans des cellules executables. Les exercices proposes permettent de consolider les acquis.

---

## Series de notebooks

### Search -- Algorithmes de recherche et optimisation

Comment un ordinateur trouve-t-il son chemin dans un labyrinthe ? Comment optimise-t-il l'ordonnancement d'un atelier ? Cette serie repond a ces questions en partant des algorithmes classiques (BFS, DFS, A*) jusqu'aux metaheuristiques modernes (recuit simule, algorithmes genetiques, essaim particulaire) et a la programmation par contraintes (OR-Tools, Z3).

Organisee en deux volets : Foundations pour la progression theorique, et Applications pour les projets concrets (Demineur CSP, Puissance 4 avec 8 IA, detection de bords par algorithmes genetiques, optimisation de portefeuille).

Python et C# | [README detaille](MyIA.AI.Notebooks/Search/README.md)

### Sudoku -- Resolution multi-paradigme

Un seul probleme -- la grille de Sudoku -- aborde par une dizaine de paradigmes differents. L'objectif n'est pas de resoudre des Sudokus, mais de comprendre les compromis entre performance, complexite d'implementation et expressivite de chaque approche.

On y decouvre le backtracking avec heuristiques MRV, la couverture exacte de Knuth (Dancing Links), les metaheuristiques (genetique, recuit simule), la programmation par contraintes (OR-Tools, Z3), et meme les reseaux de neurones. Chaque notebook est disponible en C# et Python.

C# et Python | [README detaille](MyIA.AI.Notebooks/Sudoku/README.md)

### SymbolicAI -- Raisonnement formel

L'IA symbolique s'interesse aux systemes de raisonnement automatique. Cette serie explore plusieurs sous-domaines complementaires :

**Tweety** (10 notebooks) -- Logiques formelles et argumentation computationnelle avec TweetyProject. Des extensions de Dung aux systemes ASPIC+ et DeLP, en passant par la revision de croyances AGM.

**Semantic Web** (18 notebooks) -- Du RDF/OWL aux graphes de connaissances integres aux LLMs. Fondations en .NET (dotNetRDF), standards modernes en Python (SHACL, JSON-LD, RDF-Star), puis GraphRAG et comparaison de raisonneurs.

**Lean** (13 notebooks) -- Verification formelle avec Lean 4. Types dependants, isomorphisme de Curry-Howard, tactiques Mathlib, assistance par LLM (LeanCopilot, AlphaProof). Necessite WSL sous Windows.

**Planners** (13 notebooks) -- Planification automatique : fondations PDDL, heuristiques avec Fast-Downward, planification temporelle, HTN, puis pont vers le neurosymbolique (LLM-planning).

**Smart Contracts** (27 notebooks) -- Des origines cypherpunk a Solidity avancee et aux blockchains multi-chain (Vyper, Move/Sui, Solana/Anchor). Tests Foundry, fuzz testing, verification formelle, zero-knowledge proofs, chiffrement homomorphe et DAO governance.

**Argument Analysis** (6 notebooks) -- Analyse argumentative multi-agents avec Semantic Kernel et LLMs.

Python, Lean 4 et C# | [README detaille](MyIA.AI.Notebooks/SymbolicAI/README.md)

### GameTheory -- Theorie des jeux

Comment des agents rationnels interagissent-ils ? Des equilibres de Nash aux jeux evolutionnaires, du backward induction aux jeux bayesiens, cette serie couvre les fondamentaux de la theorie des jeux et leurs applications en IA.

Les aspects avances incluent le CFR (Counterfactual Regret Minimization, au coeur des IA de poker), les jeux cooperatifs, le mechanism design et le MARL. Des side tracks en Lean 4 proposent des formalisations et preuves des theoremes classiques (Arrow, Sen).

Python et Lean 4 | [README detaille](MyIA.AI.Notebooks/GameTheory/README.md)

### Probas -- Programmation probabiliste

Comment raisonner sous incertitude ? La programmation probabiliste permet de definir des modeles generatifs, propager l'incertitude et mettre a jour des croyances face a de nouvelles observations.

La serie utilise principalement Infer.NET de Microsoft (C#) : distributions fondamentales, reseaux bayesiens, modeles de melange et theorie de la decision bayesienne. Un notebook complementaire explore la pragmatique du langage avec Pyro (modele RSA -- Rational Speech Acts).

C# (Infer.NET) et Python (Pyro) | [README Probas](MyIA.AI.Notebooks/Probas/README.md)

### ML -- Machine Learning

Les fondamentaux de l'apprentissage automatique, en deux volets :

**ML.Net** (C#) -- Introduction a l'ecosysteme Microsoft : features, entrainement, AutoML et evaluation de modeles.

**DataScienceWithAgents** (Python) -- Un parcours progressif qui part de NumPy/Pandas pour aller jusqu'aux agents IA autonomes pour la data science (Google ADK, DS-STAR, MLE-STAR), en passant par l'analyse RFP, le screening CV et la visualisation.

C# et Python | [README detaille](MyIA.AI.Notebooks/ML/README.md)

### GenAI -- IA Generative

Comment generer des images, composer de la musique, creer des videos ou converser avec un LLM ? Cette serie explore l'IA generative dans toutes ses modalites, avec une progression qui va de l'utilisation d'APIs cloud au deploiement de modeles locaux sur GPU.

Organisee par modalite, chaque domaine (Image, Audio, Video) suit une progression en quatre niveaux : Foundation (decouverte des APIs), Advanced (modeles locaux, fine-tuning), Orchestration (workflows multi-modeles) et Applications (cas d'usage concrets).

**Image** -- Generation et edition avec DALL-E 3, GPT-5, FLUX, Stable Diffusion 3.5, Qwen Image Edit. Workflows multi-modeles avec ComfyUI.

**Audio** -- Synthese vocale (OpenAI TTS, Kokoro, XTTS), transcription (Whisper), generation musicale (MusicGen), separation de sources (Demucs).

**Video** -- Comprehension video (GPT-5, Qwen-VL), generation (HunyuanVideo, LTX-Video, Wan), super-resolution (Real-ESRGAN).

**Texte** -- Prompt engineering, structured outputs, RAG, reasoning, LLMs locaux et deploiement.

**Semantic Kernel** -- L'orchestrateur IA de Microsoft, des fondamentaux a MCP et la creation de notebooks automatisee.

**Vibe-Coding** -- Ateliers pratiques sur Claude Code et Roo Code pour le developpement assiste par IA.

Python | [README detaille](MyIA.AI.Notebooks/GenAI/README.md)

### QuantConnect -- Trading algorithmique

Peut-on appliquer les techniques d'IA aux marches financiers ? Cette serie repond a cette question en combinant le framework LEAN de QuantConnect avec des approches allant du momentum classique au deep learning.

**Notebooks pedagogiques** (27 notebooks) -- Du cycle de vie d'un algorithme LEAN aux strategies ML/DL/RL/LLM, en passant par les options, futures, risk management et analyse de sentiment. Progression en cinq phases : fondations LEAN, univers et actifs, trading avance, algorithm framework, puis ML/DL/AI.

**Strategies backtestees** -- Strategies completes avec notebooks de recherche standalone (yfinance/pandas). Les approches vont du momentum multi-actifs aux modeles de facteurs Fama-French, en passant par les options couvertes et le mean reversion. Chaque strategie est accompagnee de son code source et de ses resultats de backtest.

**ML Training Pipeline** -- Pipeline complet d'entrainement et d'evaluation de modeles DL pour le forecasting financier : LSTM, Transformer, iTransformer, PatchTST, Mamba. Donnees crypto panier (10 coins) avec validation walk-forward stricte, evaluation zero-shot de modeles foundation (Chronos-Bolt, Kronos), et baselines comparatives (GARCH, random walk, majority class).

**ESGF-2026** -- Exemples de projets etudiants et notebooks de recherche issus du cours ESGF.

Python | [README detaille](MyIA.AI.Notebooks/QuantConnect/README.md) | [Strategies](MyIA.AI.Notebooks/QuantConnect/projects/README.md)

### RL -- Reinforcement Learning

Introduction a l'apprentissage par renforcement avec Stable Baselines3 : PPO sur CartPole, wrappers et callbacks, experience replay et DQN.

Python

### IIT -- Theorie de l'Information Integree

La theorie de l'information integree (Tononi) propose une approche mathematique de la conscience : un systeme est conscient dans la mesure ou il integre l'information de maniere non reducible. Ce notebook utilise PyPhi pour calculer le coefficient Phi et explorer les concepts de cause et d'effet en information.

Python | [README detaille](MyIA.AI.Notebooks/IIT/README.md)

---

## Structure du depot

```text
CoursIA/
  MyIA.AI.Notebooks/          Notebooks interactifs (500+)
    Search/                    Algorithmes de recherche (Python, C#)
    Sudoku/                    Resolution multi-paradigme (Python, C#)
    SymbolicAI/                IA symbolique (Python, Lean 4, C#)
      Tweety/ SemanticWeb/ Lean/ Planners/ SmartContracts/ Argument_Analysis/
    GameTheory/                Theorie des jeux (Python, Lean 4)
    Probas/                    Programmation probabiliste (C#, Python)
    ML/                        Machine Learning (C#, Python)
    RL/                        Reinforcement Learning (Python)
    GenAI/                     IA Generative (Python)
      Image/ Audio/ Video/ Texte/ SemanticKernel/ Vibe-Coding/
    QuantConnect/              Trading algorithmique (Python)
      Python/                  Notebooks pedagogiques
      projects/                Strategies backtestees
      ML-Training-Pipeline/    Pipeline DL forecasting
      ESGF-2026/               Projets etudiants
    EPF/                       Projets transversaux (Python)
    IIT/                       Information integree (Python)
    Config/                    Configuration API

  scripts/                     Validation, execution, analyse
  docker-configurations/       Infrastructure Docker GPU
  GradeBookApp/                Notation etudiants
  MyIA.AI.Shared/              Bibliotheque C# partagee
  notebook-infrastructure/     Papermill + MCP maintenance
```

---

## Mise en route

### Prerequis

- Python 3.10+ avec pip
- .NET 9.0 SDK (pour notebooks C#)
- VS Code avec extensions Python, Jupyter, .NET Interactive
- WSL (pour Lean et certains outils SymbolicAI)
- Docker + GPU (optionnel, pour GenAI avance)

### Installation rapide

```bash
# 1. Cloner
git clone https://github.com/jsboige/CoursIA.git
cd CoursIA

# 2. Environnement Python
python -m venv venv
venv\Scripts\activate          # Windows
pip install jupyter openai anthropic python-dotenv

# 3. Kernel Jupyter
python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"

# 4. Packages .NET (si notebooks C#)
dotnet restore MyIA.CoursIA.sln

# 5. Configuration API (selon les series souhaitees)
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env
```

### Installation par serie

La plupart des series fonctionnent directement apres le clone. Voici les dependances specifiques :

```bash
# Search / Sudoku (aucune config requise)
pip install z3-solver ortools numpy matplotlib

# Tweety (JDK auto-telecharge)
pip install jpype1 python-sat

# Lean (WSL requis)
pip install lean4_jupyter openai anthropic

# GameTheory
pip install numpy scipy matplotlib nashpy open_spiel networkx

# GenAI (Docker GPU recommande pour modeles locaux)
pip install -r MyIA.AI.Notebooks/GenAI/requirements.txt

# QuantConnect
pip install yfinance pandas numpy matplotlib
```

---

## Configuration

Les series Search, Sudoku, ML.Net, Probas (Infer.NET), Tweety, SemanticWeb et Planners fonctionnent sans aucune cle API. Les series suivantes necessitent une configuration :

| Serie | Fichier | Variables requises |
|-------|---------|-------------------|
| GenAI | `GenAI/.env` | `OPENAI_API_KEY`, `ANTHROPIC_API_KEY` |
| Lean | `SymbolicAI/Lean/.env` | `OPENAI_API_KEY`, `GITHUB_TOKEN` |
| Argument Analysis | `SymbolicAI/Argument_Analysis/.env` | `OPENAI_API_KEY` |
| QuantConnect | `QuantConnect/.env` | `QC_USER_ID`, `QC_API_TOKEN` |
| C# Notebooks | `Config/settings.json` | `apikey`, `model` |
| Docker ComfyUI | `comfyui-qwen/.env` | `CIVITAI_TOKEN`, `HF_TOKEN` |

Chaque dossier contient un `.env.example` documentant les variables. Copier et editer :

```bash
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env
# Editer le fichier .env avec vos cles
```

---

## Kernels Jupyter

| Kernel | Series | Installation |
|--------|--------|--------------|
| `python3` | Tous les notebooks Python | `pip install ipykernel` |
| `.net-csharp` | Sudoku, Search, Probas, ML | `dotnet tool install -g Microsoft.dotnet-interactive` |
| `lean4_jupyter` | Lean, GameTheory (b) | Via `elan` (WSL uniquement) |

Limitations connues : les notebooks C# avec `#!import` necessitent une execution cellule par cellule (incompatible Papermill). Lean 4 requiert WSL sous Windows.

---

## Infrastructure Docker

Pour les notebooks GenAI avances utilisant des modeles locaux (Qwen Image Edit, ComfyUI Video, etc.), une infrastructure Docker avec support GPU est fournie.

Services disponibles : Qwen Image Edit (~29 Go VRAM), ComfyUI Video (~12 Go), Stable Diffusion Forge (~10 Go), Whisper, MusicGen, Kokoro TTS, Demucs.

```bash
cd docker-configurations/services/comfyui-qwen
cp .env.example .env
docker-compose up -d
```

Configuration detaillee dans `docker-configurations/`.

---

## Scripts et validation

| Script | Usage |
|--------|-------|
| `scripts/notebook_tools/notebook_tools.py` | CLI : `validate`, `skeleton`, `analyze`, `check-env` |
| `scripts/notebook_helpers.py` | Manipulation notebooks, iteration cellules |
| `scripts/genai-stack/genai.py` | Validation stack GenAI (`validate --full`) |

```bash
# Validation structure
python scripts/notebook_tools/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku --quick

# Analyse structure
python scripts/notebook_tools/notebook_tools.py analyze MyIA.AI.Notebooks/Search

# Validation stack GenAI
python scripts/genai-stack/genai.py validate --full
```

Un workflow GitHub Actions valide automatiquement les notebooks a chaque pull request (format, syntaxe, execution de base).

---

## Outils Claude Code

Le depot inclut une configuration Claude Code avec des agents specialises et des commandes slash pour la maintenance des notebooks.

**Commandes principales** : `/verify-notebooks`, `/enrich-notebooks`, `/cleanup-notebooks`, `/build-notebook`, `/execute-notebook`, `/validate-genai`, `/qc-iterative-improve`

**Agents specialises** : notebook-enricher, notebook-validator, notebook-executor, qc-strategy-analyzer, qc-strategy-improver, readme-updater, et d'autres.

Configuration dans `.claude/agents/` et `.claude/skills/`.

---

## Outils et dependances externes

Les dependances principales par serie :

| Outil | Series | Installation |
|-------|--------|--------------|
| Z3 SMT Solver | Sudoku, Search, SymbolicAI | `pip install z3-solver` |
| OR-Tools | Sudoku, Search, Planners | `pip install ortools` |
| Tweety + JDK | Tweety, Argument_Analysis | Auto-telecharge |
| Lean 4 + Mathlib | Lean, GameTheory | Via `elan` (WSL) |
| OpenSpiel | GameTheory 13-17 | `pip install open_spiel` |
| Infer.NET | Probas | Via NuGet |
| PyPhi | IIT | `pip install pyphi` |

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

Repository : [github.com/jsboige/CoursIA](https://github.com/jsboige/CoursIA)

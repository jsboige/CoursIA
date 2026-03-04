# CoursIA

**Apprendre l'intelligence artificielle par la pratique, de la theorie aux applications.**

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## Bienvenue

CoursIA est une plateforme educative de **300+ notebooks Jupyter** couvrant l'ensemble du spectre de l'IA : des algorithmes classiques de recherche jusqu'a la generation d'images, de video et de musique par IA, en passant par la theorie des jeux, la verification formelle et le trading algorithmique.

Chaque serie est concue comme un cours complet avec une progression pedagogique, des exercices pratiques et des comparaisons d'approches. Les notebooks sont disponibles en Python, C# (.NET Interactive) et Lean 4.

**Tout est gratuit et open source.** La plupart des series fonctionnent entierement en local. Seules les series GenAI et QuantConnect necessitent des cles API (gratuites).

## Par ou commencer ?

Selon votre profil :

**Debutant en IA** -- Commencez par [ML](#ml---machine-learning) pour les fondamentaux (ML.NET ou Python), puis [Search](#search---recherche-et-optimisation) pour les algorithmes classiques. La serie [Sudoku](#sudoku---un-probleme-toutes-les-approches) est parfaite pour comprendre les compromis entre paradigmes.

**Developpeur C#/.NET** -- Les series [Probas/Infer.NET](#probas---programmation-probabiliste), [Sudoku](#sudoku---un-probleme-toutes-les-approches) et [ML.NET](#ml---machine-learning) exploitent l'ecosysteme Microsoft. Vous y trouverez des equivalents C# pour la plupart des approches Python.

**Data Scientist Python** -- [GenAI](#genai---ia-generative) pour maitriser les LLMs et la generation multimodale, [QuantConnect](#quantconnect---trading-algorithmique) pour appliquer le ML a la finance, et [GameTheory](#gametheory---theorie-des-jeux) pour la prise de decision strategique.

**Chercheur en IA symbolique** -- [SymbolicAI](#symbolicai---raisonnement-formel) offre un parcours complet : logiques formelles (Tweety), Web Semantique (RDF/OWL), verification de preuves (Lean 4), planification (PDDL/Fast-Downward) et smart contracts (Solidity).

**Curieux de GenAI** -- La serie [GenAI](#genai---ia-generative) est autonome. Commencez par Texte (LLMs), puis explorez Image, Audio et Video selon vos interets.

---

## Series de notebooks

### Search - Recherche et Optimisation

Les algorithmes de recherche sont le socle de l'IA. Cette serie vous guide de la formalisation des espaces d'etats aux metaheuristiques, avec deux volets : **Foundations** (theorie progressive) et **Applications** (problemes reels adaptes de projets etudiants EPITA, EPF, ECE).

Vous apprendrez a choisir l'algorithme adapte (BFS, DFS, A*, algorithmes genetiques, recuit simule, PSO), implementer des contraintes avec OR-Tools et Z3, et appliquer ces techniques a des problemes comme l'ordonnancement d'atelier, le Demineur CSP ou Puissance 4 avec 8 IA differentes.

31 notebooks -- Python et C# -- [README detaille](MyIA.AI.Notebooks/Search/README.md)

### Sudoku - Un probleme, toutes les approches

Ce qui rend cette serie unique : le **meme probleme** resolu par une dizaine de paradigmes differents. Backtracking, Dancing Links, algorithmes genetiques, OR-Tools, Z3 SMT, Infer.NET bayesien, reseaux de neurones, LLMs... Vous comprendrez concraitrement les compromis performance/complexite/expressivite de chaque approche.

31 notebooks -- C# et Python (miroir) -- [README detaille](MyIA.AI.Notebooks/Sudoku/README.md)

### SymbolicAI - Raisonnement Formel

L'IA symbolique couvre les systemes de raisonnement automatique, des syllogismes d'Aristote aux assistants de preuves modernes. Cette serie regroupe plusieurs sous-domaines complementaires :

**Tweety** (10 notebooks) -- Logiques formelles (propositionnelle, premier ordre, description) et argumentation computationnelle avec TweetyProject. Calculez des extensions de Dung, modelisez des dialogues multi-agents, explorez ASPIC+ et DeLP.

**Semantic Web** (18 notebooks) -- Du RDF/OWL aux graphes de connaissances integres aux LLMs. Vous commencerez avec .NET (dotNetRDF) puis transitionnerez vers Python pour les standards modernes (SHACL, JSON-LD, RDF-Star). La serie se conclut par GraphRAG et la comparaison de raisonneurs OWL.

**Lean** (11 notebooks) -- Verification formelle avec Lean 4. Des fondements (types dependants, Curry-Howard) aux tactiques Mathlib, puis l'assistance par LLMs (LeanCopilot, AlphaProof) et TorchLean (reseaux de neurones formellement verifies). Necessite WSL sous Windows.

**Planners** (13 notebooks) -- Planification automatique : PDDL, Fast-Downward, heuristiques, OR-Tools scheduling, planification temporelle, HTN, et l'integration LLM-planning (neurosymbolique).

**Smart Contracts** (17 notebooks) -- De Solidity aux blockchains multi-chain (Move/Sui, Solana/Anchor). Tests avec Foundry, fuzz testing, verification formelle de smart contracts, DAO governance et account abstraction.

**Argument Analysis** (6 notebooks) -- Analyse argumentative multi-agents avec Semantic Kernel et LLMs.

70+ notebooks -- Python, Lean 4, C# -- [README detaille](MyIA.AI.Notebooks/SymbolicAI/README.md)

### GameTheory - Theorie des Jeux

Des jeux statiques aux strategies multi-agent. Equilibres de Nash, strategies mixtes, jeux evolutionnaires et repetes, backward induction, jeux bayesiens. Vous implementerez CFR (Counterfactual Regret Minimization) avec OpenSpiel -- l'algorithme qui a permis aux IA de dominer le poker. Des side tracks en Lean 4 offrent des preuves formelles des theoremes classiques.

26 notebooks -- Python et Lean 4 -- [README detaille](MyIA.AI.Notebooks/GameTheory/README.md)

### Probas - Programmation Probabiliste

Avec Infer.NET de Microsoft, vous apprendrez a definir des modeles probabilistes, propager l'incertitude et mettre a jour vos croyances face a de nouvelles observations. La serie couvre les distributions fondamentales, les reseaux bayesiens, et se termine par la theorie de la decision sous incertitude. Un notebook supplementaire explore la pragmatique du langage avec Pyro (RSA).

22 notebooks -- C# (Infer.NET) et Python (Pyro) -- [README detaille](MyIA.AI.Notebooks/Probas/README.md)

### ML - Machine Learning

Les fondamentaux de l'apprentissage automatique, avec plusieurs volets :

**ML.NET** -- Introduction a l'ecosysteme Microsoft ML.NET : features, entrainement, AutoML, evaluation.

**Python Data Science** -- NumPy, Pandas et les bases du pipeline Data Science.

**AI Agents Workshop** -- Construction d'agents IA pour l'analyse RFP, le screening CV et le data wrangling.

**Agentic Data Science** -- Parcours complet avec Google ADK, DS-STAR et MLE-STAR pour la data science augmentee par agents IA.

**Reinforcement Learning** -- Stable Baselines3 : PPO, SAC/DDPG, HER pour l'apprentissage par renforcement.

27 notebooks -- C# et Python -- [README detaille](MyIA.AI.Notebooks/ML/README.md)

### GenAI - IA Generative

La serie la plus vaste du depot, organisee par modalite avec une progression en 4 niveaux (Foundation, Advanced, Orchestration, Applications) :

**Image** (19 notebooks) -- DALL-E 3, GPT-5, FLUX, Stable Diffusion 3.5, Qwen Image Edit. De la generation simple aux workflows multi-modeles avec ComfyUI.

**Audio** (16 notebooks) -- Synthese vocale (OpenAI TTS, Kokoro, XTTS), transcription (Whisper), generation musicale (MusicGen), separation de sources (Demucs).

**Video** (16 notebooks) -- Comprehension video (GPT-5, Qwen-VL), generation (AnimateDiff, HunyuanVideo, LTX-Video, Wan, SVD), super-resolution (Real-ESRGAN).

**Texte** (10 notebooks) -- Prompt engineering, structured outputs, RAG, reasoning, local LLMs, production deployment.

**Semantic Kernel** (20 notebooks) -- L'orchestrateur IA de Microsoft, des fondamentaux a MCP et la creation de notebooks automatisee.

**Vibe-Coding** (5 notebooks) -- Ateliers pratiques sur Claude Code et Roo Code pour le developpement assiste par IA.

96 notebooks -- Python -- [README detaille](MyIA.AI.Notebooks/GenAI/README.md)

### QuantConnect - Trading Algorithmique

Application concrete de l'IA a la finance quantitative. La serie comprend deux volets :

**Notebooks pedagogiques** (27 notebooks) -- Du cycle de vie d'un algorithme LEAN aux strategies ML/DL/RL/LLM, en passant par les options, futures, risk management et analyse de sentiment.

**Strategies backtestees** (10 projets) -- Strategies completes avec notebooks de recherche standalone (yfinance/pandas). Chaque strategie a ete iterativement optimisee :

| Strategie | Approche | Sharpe |
|-----------|----------|--------|
| SectorMomentum | Dual Momentum SPY/TLT/GLD | 0.554 |
| OptionsIncome | Covered Call SPY + VIX filter | 0.747 |
| FamaFrench | Factor ETF rotation (5 facteurs) | 0.471 |
| MomentumStrategy | Rotation 11 ETFs sectoriels | 0.411 |
| AllWeather | Portfolio multi-asset Dalio | 0.365 |

[README detaille](MyIA.AI.Notebooks/QuantConnect/README.md) | [Projets](MyIA.AI.Notebooks/QuantConnect/projects/README.md)

### IIT - Information Integree

La theorie de l'information integree (Tononi) propose une approche mathematique de la conscience : un systeme est conscient dans la mesure ou il integre l'information de maniere non reducible. Ce notebook vous initie a PyPhi pour calculer le coefficient Phi et identifier les complexes maximaux.

1 notebook -- Python -- [README detaille](MyIA.AI.Notebooks/IIT/README.md)

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
git clone https://github.com/jsboige/CoursIA.git
cd CoursIA

# Environnement Python
python -m venv venv
venv\Scripts\activate  # Windows
pip install jupyter openai anthropic python-dotenv

# Packages .NET (si notebooks C#)
dotnet restore MyIA.CoursIA.sln
```

La plupart des series (Search, Sudoku, Probas, Tweety, SemanticWeb) fonctionnent immediatement sans configuration supplementaire. Pour GenAI et QuantConnect, copiez les fichiers `.env.example` et ajoutez vos cles API.

### Configuration API (si necessaire)

```bash
# GenAI
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env

# QuantConnect
cp MyIA.AI.Notebooks/QuantConnect/.env.example MyIA.AI.Notebooks/QuantConnect/.env

# C# Notebooks (OpenAI)
cp MyIA.AI.Notebooks/Config/settings.json.openai-example MyIA.AI.Notebooks/Config/settings.json
```

---

## Infrastructure et outils

### Docker GPU (optionnel)

Pour la generation d'images avancee, une infrastructure Docker est disponible avec ComfyUI comme orchestrateur. Les modeles Qwen Image Edit et FLUX necessitent respectivement ~29 Go et ~10 Go de VRAM.

```bash
cd docker-configurations/services/comfyui-qwen
cp .env.example .env
docker-compose up -d
```

### Scripts de validation

```bash
# Validation notebooks
python scripts/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku --quick

# Validation stack GenAI
python scripts/genai-stack/genai.py validate --full
```

### Outils Claude Code

Ce depot est optimise pour Claude Code avec des agents specialises (enrichissement, validation, execution) et des commandes slash (`/verify-notebooks`, `/enrich-notebooks`, `/build-notebook`). Voir `.claude/agents/` et `.claude/skills/`.

---

## Contribution

1. Fork le depot
2. Creer une branche (`git checkout -b feature/nouveau-notebook`)
3. Commit (`git commit -m 'Add: notebook sur les Transformers'`)
4. Push et ouvrir une Pull Request

Conventions : PEP 8 pour Python, pas d'emojis dans le code, documentation en francais.

## Licence

Ce projet est sous licence MIT - voir [LICENSE](LICENSE).

---

Repository : https://github.com/jsboige/CoursIA

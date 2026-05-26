# MyIA.AI.Notebooks - Ecosysteme de Notebooks CoursIA

Ecosysteme complet de **555 notebooks** Jupyter pour l'apprentissage des technologies AI/ML modernes, organisé par domaines thématiques.

<!-- CATALOG-STATUS
series: ALL
total: 492
breakdown: GenAI=112, QuantConnect=102, SymbolicAI=92, Search=45, Probas=43, Sudoku=32, ML=30, GameTheory=25, RL=6, CaseStudies=4, IIT=1
maturity: BETA=278, PRODUCTION=153, ALPHA=46, DRAFT=11, TEMPLATE=4
-->

Dernière mise à jour : 2026-05-23

## Vue d'ensemble

| Domaine | Notebooks | Description |
|---------|-----------|-------------|
| **GenAI** | 110 | IA Generative (Images, Audio, Video, Texte, Vibe-Coding) |
| **QuantConnect** | 175 | Trading algorithmique et ML financier (Python + C#) |
| **SymbolicAI** | 92 | IA Symbolique (Lean, Tweety, SmartContracts, SemanticWeb, Planners) |
| **Search** | 45 | Recherche, CSP, optimisation, metaheuristiques |
| **Sudoku** | 32 | Resolution de contraintes (.NET C#) |
| **Probas** | 32 | Programmation probabiliste (Infer.NET + PyMC) |
| **ML** | 30 | Machine Learning .NET + Python Agents for Data Science |
| **GameTheory** | 28 | Theorie des Jeux (OpenSpiel, choix social Lean) |
| **RL** | 6 | Reinforcement Learning (Stable-Baselines3) |
| **CaseStudies** | 4 | Etudes de cas interdisciplinaires (diagnostic medical, planification oncologique) |
| **IIT** | 1 | Integrated Information Theory (PyPhi) |

### Progression pedagogique

```text
GenAI (110 notebooks)
├── Image/ (19) - Generation d'images
├── Audio/ (28) - Traitement audio
├── Video/ (16) - Traitement video
├── Texte/ (11) - LLMs et texte
├── SemanticKernel/ (20) - SDK Microsoft
├── CaseStudies/ (4) - Etudes de cas etudiants
└── Vibe-Coding/ (5) - Claude-Code + Roo-Code

QuantConnect (175 notebooks)
├── Python/ (53) - Cours progressifs QC-Py
├── projects/ (109) - Strategies backtests et ML
└── ESGF-2026/ (7) - Cours ESGF exercices et templates

SymbolicAI (92 notebooks)
├── SmartContracts/ (27) - Solidity, Web3, blockchain
├── SemanticWeb/ (18) - RDF, SPARQL, OWL, C# + Python
├── Planners/ (14) - PDDL, Fast-Downward, OR-Tools, LLM planning
├── Lean/ (14) - Theorem proving, LeanDojo
├── Tweety/ (10) - Logiques classiques, argumentation
└── Argument_Analysis/ (6) - Analyse d'arguments
```

## Technologies principales

### AI/ML
- **OpenAI**: GPT-4o, GPT-5, DALL-E 3
- **Anthropic**: Claude (via API / Claude Code)
- **Hugging Face**: Transformers, Diffusers
- **Microsoft**: Semantic Kernel, .NET 9
- **Locaux**: vLLM, Ollama, Qwen 2.5, Chronos

### QuantConnect / Finance
- **LEAN Engine**: Backtesting, live trading, optimisation
- **sklearn / XGBoost / PyTorch**: Modeles ML financiers
- **QuantConnect Cloud**: 95 projets, backtests cloud
- **Hands-On AI Trading**: 18/19 exemples implementes (issue #143)

### Infrastructure
- **Docker**: ComfyUI (29GB VRAM), services GenAI
- **MCP**: Jupyter automation, QuantConnect MCP server
- **Papermill**: Execution batch

### Domaines d'etude
- **Computer Vision**: Image, Video, Animation
- **NLP**: LLMs, RAG, Reasoning, Sentiment
- **Audio**: STT, TTS, Voice Cloning, Music
- **Finance**: Trading algorithmique, ML financier, options
- **Symbolic**: RDF, Z3 SMT, Lean 4, SmartContracts
- **Optimization**: CSP, metaheuristiques, recherche operationnelle

## Liens vers les sous-domaines

| Domaine | Notebooks | Lien |
|---------|-----------|------|
| **GenAI** | 110 | [GenAI/](GenAI/README.md) |
| **QuantConnect** | 175 | [QuantConnect/](QuantConnect/README.md) |
| **SymbolicAI** | 92 | [SymbolicAI/](SymbolicAI/README.md) |
| **Search** | 45 | [Search/](Search/README.md) |
| **Sudoku** | 32 | [Sudoku/](Sudoku/README.md) |
| **Probas** | 32 | [Probas/](Probas/README.md) |
| **ML** | 30 | [ML/](ML/README.md) |
| **GameTheory** | 28 | [GameTheory/](GameTheory/README.md) |
| **RL** | 6 | [RL/](RL/README.md) |
| **CaseStudies** | 4 | [CaseStudies/](CaseStudies/README.md) |
| **IIT** | 1 | [IIT/](IIT/README.md) |

## Configuration requise

### Environnement
- Python 3.10+ avec venv
- .NET 9.0 SDK
- Docker (services GenAI)
- 24GB+ VRAM (recommandé pour GenAI)

### Installation
```bash
# Python
cd MyIA.AI.Notebooks/GenAI
python -m venv venv && venv\Scripts\activate
pip install -r requirements.txt

# C#
dotnet restore MyIA.CoursIA.sln
```

### Services Docker
```bash
# Démarrer ComfyUI (nécessaire pour Image/Video)
cd docker-configurations/services/comfyui-qwen
docker-compose up -d
```

## Parcours recommande

### Debutant (30h)
1. **GenAI/00-Environment** - Setup complet
2. **GenAI/Image/01-Foundation** - Bases images
3. **GenAI/Audio/01-Foundation** - Bases audio
4. **QuantConnect/Python/** - Cours QC-Py-01 a 10

### Intermediaire (60h)
1. **GenAI** - Toutes les series sauf Orchestration
2. **ML** - Tutoriels .NET + Python Agents
3. **SymbolicAI** - SmartContracts, SemanticWeb
4. **QuantConnect/ESGF-2026/** - Exercices trading

### Expert (120h+)
1. **GenAI/03-Orchestration** + **04-Applications**
2. **SymbolicAI** - Lean, Planners, Tweety avance
3. **Search**, **GameTheory**, **Probas** - Domaines avances
4. **QuantConnect/projects/** - Strategies ML avancees

## Ressources

### Documentation
- [CLAUDE.md](../CLAUDE.md) - Configuration projet
- [GenAI Documentation](GenAI/README.md) - IA Generative
- [QuantConnect Documentation](QuantConnect/README.md) - Trading algorithmique
- [Scripts](../scripts/) - Outils d'automatisation

### Validation

```bash
# Valider les notebooks
python scripts/notebook_tools/notebook_tools.py validate GenAI --quick
python scripts/notebook_tools/notebook_tools.py validate MyIA.AI.Notebooks/ML --quick

# Executer en batch
python scripts/notebook_tools/notebook_tools.py execute GenAI --timeout 300
```

---

Architecture SDDD | Compatible MCP

# MyIA.AI.Notebooks - Ecosysteme de Notebooks CoursIA

CoursIA est un curriculum d'intelligence artificielle pensé comme un parcours continu, des fondations jusqu'aux frontières de la recherche. Plutôt qu'une collection d'exemples isolés, il tisse un même fil conducteur à travers onze domaines : on y apprend autant à **faire** — générer des images et de l'audio, entraîner et déployer des modèles, backtester des stratégies de trading, résoudre des problèmes de contraintes — qu'à **comprendre et prouver** : formaliser un théorème en Lean 4, raisonner sur l'incertitude, vérifier qu'un smart contract ou un algorithme se comporte comme attendu.

Deux partis pris structurent l'ensemble. D'abord une **double culture technique** : Python (PyTorch, Diffusers, PyMC, OpenSpiel) et .NET / C# (Semantic Kernel, Infer.NET, ML.NET) cohabitent au sein de notebooks exécutables, parce que l'IA appliquée se pratique dans les deux écosystèmes. Ensuite une **dualité simulation / preuve** : un concept est d'abord illustré numériquement, puis — quand c'est possible — formalisé et vérifié mécaniquement (Lean 4, Z3, vérification formelle). Chaque notebook est rédigé en français, exécutable de bout en bout, et accompagné d'exercices corrigés pour un apprentissage en autonomie.

Le catalogue rassemble près de 500 notebooks répartis sur les onze domaines ci-dessous (le décompte exact par série est tenu à jour automatiquement dans le marqueur de catalogue). Une bonne porte d'entrée : **GenAI** pour la création assistée par IA, **QuantConnect** pour le ML appliqué à un domaine concret, ou **Search / GameTheory / SymbolicAI** pour les fondements algorithmiques et formels.

<!-- CATALOG-STATUS
series: ALL
total: 515
breakdown: GenAI=120, SymbolicAI=104, QuantConnect=101, Search=46, Probas=44, Sudoku=32, ML=27, GameTheory=25, RL=10, CaseStudies=4, IIT=2
maturity: PRODUCTION=410, ALPHA=53, BETA=44, DRAFT=4, TEMPLATE=4
-->

Dernière mise à jour : 2026-05-28

## Vue d'ensemble

| Domaine | Description |
|---------|-------------|
| **GenAI** | Generation d'images (SDXL, Flux, Qwen-VL), audio (FishAudio S2-Pro, STT/TTS), video, LLMs, RAG, fine-tuning LoRA, orchestration via Semantic Kernel |
| **QuantConnect** | Trading algorithmique progressif : cours Python pas-a-pas, 49 strategies backtestees (GARCH, Kelly, ensemble), pipeline ML thermal-safe |
| **SymbolicAI** | Preuve formelle Lean 4 (theoremes d'Arrow, Conway, Kochen-Specker), logiques argumentaires (Tweety), SmartContracts Solidity, Web semantique RDF/SPARQL |
| **Search** | Satisfaction de contraintes (CSP), recherche operationnelle, metaheuristiques (recuit, genetiques), planification PDDL avec Fast-Downward |
| **Probas** | Programmation probabiliste : modeles graphiques en Infer.NET (.NET C#) + inference bayesienne en PyMC (Python) |
| **Sudoku** | Resolution de contraintes en .NET C# : backtracking, propagation, modeles CNN/MLP, etude comparative d'architectures |
| **GameTheory** | Theorie des jeux combinatoire (OpenSpiel), choix social formel (theoremes d'Arrow, Sen, Shapley portes en Lean 4), von Neumann |
| **ML** | Machine Learning .NET (ML.NET) + Python Agents for Data Science : classification, regression, clustering, pipelines |
| **RL** | Reinforcement Learning avec Stable-Baselines3 : environnements OpenAI Gym, PPO, SAC, evaluation de politiques |
| **CaseStudies** | Etudes de cas interdisciplinaires : diagnostic medical par LLM, planification oncologique, analyse de sentiments |
| **IIT** | Integrated Information Theory : mesures Phi avec PyPhi, neurones logiques, conscience et complexite |

### Progression pedagogique

```text
GenAI
├── 00-GenAI-Environment/ - Setup Docker, GPU, services
├── Image/ - Generation d'images (SDXL, Qwen, Flux)
├── Audio/ - STT, TTS, music, pipeline audiobook FishAudio S2-Pro
├── Video/ - Generation video, animation
├── Texte/ - LLMs, RAG, reasoning
├── SemanticKernel/ - SDK Microsoft
├── FineTuning/ - Fine-tuning LoRA, adapters
├── CaseStudies/ - Etudes de cas etudiants
└── Vibe-Coding/ - Claude-Code + Roo-Code

QuantConnect
├── Python/ - Cours progressifs QC-Py (fondamentaux → strategies)
├── projects/ - Strategies backtestees et ML (GARCH, Kelly, ensemble)
└── ML-Training-Pipeline/ - Pipeline training thermal-safe

SymbolicAI
├── SmartContracts/ - Solidity, Web3, blockchain
├── SemanticWeb/ - RDF, SPARQL, OWL, C# + Python
├── Lean/ - Theorem proving, LeanDojo, social choice
├── Planners/ - PDDL, Fast-Downward, OR-Tools, LLM planning
├── Tweety/ - Logiques classiques, argumentation
├── SymbolicLearning/ - ILP, NeuroSymbolic, KG-ILP, LLM-Symbolic
└── Argument_Analysis/ - Analyse d'arguments
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

| Domaine | Lien |
|---------|------|
| **GenAI** | [GenAI/](GenAI/README.md) |
| **QuantConnect** | [QuantConnect/](QuantConnect/README.md) |
| **SymbolicAI** | [SymbolicAI/](SymbolicAI/README.md) |
| **Search** | [Search/](Search/README.md) |
| **Probas** | [Probas/](Probas/README.md) |
| **Sudoku** | [Sudoku/](Sudoku/README.md) |
| **GameTheory** | [GameTheory/](GameTheory/README.md) |
| **ML** | [ML/](ML/README.md) |
| **RL** | [RL/](RL/README.md) |
| **CaseStudies** | [CaseStudies/](CaseStudies/README.md) |
| **IIT** | [IIT/](IIT/README.md) |

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
4. **QuantConnect/partner-course-quant-trading/** - Exercices trading

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

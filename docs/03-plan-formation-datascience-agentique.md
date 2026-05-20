# Plan de Formation : Data Science Agentique (Edition 2026)

Ce parcours forme des developpeurs a la data science moderne ou l'IA generative et les agents autonomes sont au coeur du workflow. Il couvre les fondamentaux Python, la maitrise multi-modale (image, audio, video, texte), l'orchestration d'agents (Semantic Kernel, Claude Code, Roo Code), et l'application au trading algorithmique via QuantConnect.

---

## Comment utiliser ce parcours

Chaque module correspond a une serie de notebooks Jupyter presentes dans le depot, accompagnes de README detailles par sous-domaine. Les notebooks sont structures en 4 niveaux de progression :

- **Foundation** : decouverte des concepts et premiers pas pratiques
- **Advanced** : techniques specialisees et modeles avances
- **Orchestration** : combinaison de plusieurs modeles et pipelines
- **Applications** : cas d'usage concrets et projets de production

La duree totale est d'environ 120-150 heures, repartissable sur un semestre universitaire ou une formation intensive.

---

## Module 1 : Les Fondamentaux Python pour la Data Science

Ce module pose les bases techniques : manipulation de donnees, visualisation, et introduction au machine learning. Il ne necessite aucune experience prealable en IA.

**Competences acquises** : NumPy (tableaux vectorises), Pandas (DataFrames, nettoyage), Matplotlib/Seaborn (visualisation), Scikit-Learn (cycle de vie ML).

Ce module est transversal : les competences acquises ici sont utilisees dans tous les modules suivants. La pratique se fait via des notebooks d'exercices dans `MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/` pour le setup, puis dans les series specialisees.

---

## Module 2 : IA Generative Multi-Modale

Le coeur du parcours. On apprend a generer et manipuler du contenu avec des modeles d'IA : images, audio, video, texte. Chaque modalite suit la progression Foundation/Advanced/Orchestration/Applications.

### 2a. Generation d'Images

**Ce qu'on apprend** : utiliser DALL-E 3, GPT-5 et des modeles open-source (Qwen Image Edit, FLUX, Stable Diffusion, Lumina) pour generer, editer et orchestrer des images. Les notebooks avances couvrent le ComfyUI pour les workflows GPU locaux.

**Fil rouge** : creer un generateur de contenu visuel pour l'education (diagrammes scientifiques, illustrations pedagogiques, motifs decoratifs).

Emplacement : `MyIA.AI.Notebooks/GenAI/Image/` (19 notebooks, ~8h)

### 2b. Speech, Voix et Musique

**Ce qu'on apprend** : reconnaissance vocale (Whisper V3), synthese vocale (Kokoro, OpenAI TTS), clonage de voix (XTTS), generation musicale (MusicGen), et separation de sources (Demucs). Les notebooks avances explorent la generation de chansons completes et le TTS expressif.

**Fil rouge** : produire un podcast automatique avec voix synthetique personnalisee et fond musical genere.

Emplacement : `MyIA.AI.Notebooks/GenAI/Audio/` (21 notebooks, ~16h)

### 2c. Video

**Ce qu'on apprend** : comprehension video (GPT-5, Qwen-VL), generation (HunyuanVideo, Wan, Sora), et workflows de production video par IA. Les notebooks couvrent aussi le surcadrage d'images et la synchronisation audio-video.

**Fil rouge** : creer une video pedagogique automatisee depuis un script texte.

Emplacement : `MyIA.AI.Notebooks/GenAI/Video/` (16 notebooks, ~14h)

### 2d. LLMs et Generation de Texte

**Ce qu'on apprend** : maitriser les APIs OpenAI (prompt engineering, structured outputs, function calling, RAG, code interpreter). Les notebooks avances couvrent les modeles de raisonnement et les patterns de production.

Emplacement : `MyIA.AI.Notebooks/GenAI/Texte/` (10 notebooks, ~10h)

### Infrastructure Docker

Les services GenAI tournent en Docker avec acceleration GPU (RTX 3090). Le setup est documente dans `00-GenAI-Environment/` et les scripts de gestion dans `scripts/genai-stack/`. La validation de l'environnement se fait via `/validate-genai`.

---

## Module 3 : Developpement Agentique (Vibe Coding)

Ce module introduit le "vibe coding" : le developpement logiciel assiste par des agents IA autonomes. C'est la competence la plus demandee du marche en 2026.

**Ce qu'on apprend** : utiliser Claude Code et Roo Code comme assistants de developpement, orchestrer des taches complexes, creer des workflows automatises, et integrer des serveurs MCP (Model Context Protocol).

**Fil rouge** : creer un agent autonome capable d'analyser un jeu de donnees, generer un rapport visuel, et le deployer en production.

Emplacement : `MyIA.AI.Notebooks/GenAI/Vibe-Coding/` (Claude Code : 5 modules, Roo Code : 5 modules + ateliers, ~30h)

---

## Module 4 : Orchestration avec Microsoft Semantic Kernel

Semantic Kernel est le SDK Microsoft pour integrer des LLMs dans des applications .NET et Python. Ce module couvre les plugins, les agents, les filtres, les vector stores, et les pipelines multi-etapes.

**Ce qu'on apprend** : construire des architectures agentiques robustes avec orchestration de plugins, gestion de contexte, et integration multi-modale.

Emplacement : `MyIA.AI.Notebooks/GenAI/SemanticKernel/` (20 notebooks, ~20h)

---

## Module 5 : ML pour le Trading Algorithmique (QuantConnect)

Application avancee : utiliser le machine learning pour predire les marches financiers, avec une methode scientifique rigoureuse (walk-forward validation, multi-seed, baselines).

**Ce qu'on apprend** : le pipeline ML complet applique au trading (feature engineering, modeles RF/XGBoost/Transformer/LSTM, evaluation hors-sample), les pieges du ML financier (surapprentissage, survivorship bias), et la validation croisee temporelle.

**Reference** : *Hands-On AI Trading* (Jared Broad, 2025), [hands-on-ai-trading.com](https://www.hands-on-ai-trading.com/)

Emplacement : `MyIA.AI.Notebooks/QuantConnect/` (50+ strategies, pipeline ML dans `ML-Training-Pipeline/`)

---

## Module 6 : Tests E2E et Qualite Logicielle

Les agents IA doivent etre testes rigoureusement. Ce module couvre Playwright pour les tests de bout en bout sur des applications GenAI reelles (Open WebUI).

Emplacement : `MyIA.AI.Notebooks/GenAI/Playwright-OWUI/` (5 modules, 30+ tests)

---

## Progression recommandee

| Profil                              | Modules             | Duree  |
|-------------------------------------|---------------------|--------|
| **Decouvreur** (initiation rapide)  | 1 + 2a ou 2b        | ~20h   |
| **Praticien** (maitrise multi-modale) | 1 + 2a-d          | ~50h   |
| **Agentiste** (full-stack agentic)  | 1 + 2 + 3 + 4       | ~90h   |
| **Expert** (avec trading ML)        | 1 + 2 + 3 + 4 + 5   | ~130h  |

---

## Ressources complementaires

- Documentation services GenAI : `docs/genai-services.md`
- Configuration Claude Code : `docs/claude-code-config.md`
- Infrastructure QuantConnect : `docs/quantconnect.md`
- Validation notebooks : `python scripts/notebook_tools/notebook_tools.py validate <path>`
- Validation GenAI stack : `/validate-genai`

---

*Document mis a jour mai 2026. Pour l'historique de la version originale (ADK DeepMind 2023), voir `docs/02-etude-adk-deepmind.md`.*

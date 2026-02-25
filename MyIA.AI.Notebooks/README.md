# MyIA.AI.Notebooks - Ecosysteme de Notebooks CoursIA

Ecosysteme complet de notebooks Jupyter pour l'apprentissage des technologies AI/ML modernes, organisé par domaines thématiques.

## Vue d'ensemble

| Domaine | Notebooks | Statut | Description |
|---------|-----------|--------|-------------|
| **GenAI** | 127 | 93.7% | Intelligence Artificielle Générative (Images, Audio, Video, Texte) |
| **ML.NET** | 15 | - | Machine Learning avec .NET |
| **SymbolicAI** | 20 | - | IA Symbolique (RDF, Z3, Lean) |
| **Game Theory** | 12 | - | Théorie des Jeux et OpenSpiel |
| **Sudoku** | 8 | - | Resolution de contraintes |
| **Probas** | 10 | - | Programmation probabiliste (Infer.NET) |
| **Search** | 15 | - | Optimisation et recherche |
| **IIT** | 8 | - | Integrated Information Theory |
| **GradeBook** | 1 | - | Système de notation |

### Progression pédagogique

```
GenAI (127 notebooks)
├── 00-Environment (6) - Setup
├── Image (19) - Génération d'images
├── Audio (16) - Traitement audio
├── Video (16) - Traitement video
├── Texte (10) - LLMs et texte
├── SemanticKernel (14) - SDK Microsoft
├── EPF (4) - Projets étudiants
└── Vibe-Coding (42) - Développeurs
```

## Technologies principales

### AI/ML
- **OpenAI**: GPT-4o, GPT-5, DALL-E 3
- **Hugging Face**: Transformers, Diffusers
- **Microsoft**: Semantic Kernel, .NET 9
- **Locaux**: vLLM, Ollama, Qwen 2.5

### Infrastructure
- **Docker**: ComfyUI (29GB VRAM), services GenAI
- **MCP**: Jupyter automation
- **Papermill**: Execution batch

### Domaines d'étude
- **Computer Vision**: Image, Video, Animation
- **NLP**: LLMs, RAG, Reasoning
- **Audio**: STT, TTS, Voice Cloning, Music
- **ML.NET**: C# ML, Infer.NET
- **Symbolic**: RDF, Z3 SMT, Lean 4

## Liens vers les sous-domaines

| Domaine | Description | Lien |
|---------|-------------|------|
| **GenAI** | IA Générative multimodale | [GenAI/](GenAI/README.md) |
| **ML.NET** | Tutoriels .NET Interactive | [ML/](ML/README.md) |
| **SymbolicAI** | IA Symbolique et formelle | [SymbolicAI/](SymbolicAI/README.md) |
| **Game Theory** | Théorie des Jeux WSL | [GameTheory/](GameTheory/README.md) |
| **Sudoku** | Constraint solving | [Sudoku/](Sudoku/README.md) |
| **Probas** | Programmation probabiliste | [Probas/](Probas/README.md) |
| **Search** | Recherche et optimisation | [Search/](Search/README.md) |
| **IIT** | Integrated Information Theory | [IIT/](IIT/README.md) |

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

## Parcours recommandé

### Débutant (30h)
1. **GenAI/00-Environment** - Setup complet
2. **GenAI/Image/01-Foundation** - Bases images
3. **GenAI/Audio/01-Foundation** - Bases audio
4. **GenAI/Video/01-Foundation** - Bases video

### Intermédiaire (60h)
1. **GenAI** - Toutes les séries sauf Orchestration
2. **ML.NET** - Tutoriels de base
3. **SymbolicAI** - Introduction

### Expert (120h+)
1. **GenAI/03-Orchestration** + **04-Applications**
2. **Game Theory**, **IIT** - Domaines avancés
3. **Probas**, **Search** - Optimisation

## Ressources

### Documentation
- [CLAUDE.md](../CLAUDE.md) - Configuration projet
- [GenAI Documentation](GenAI/README.md) - IA Générative
- [Scripts](../scripts/) - Outils d'automatisation

### Validation
```bash
# Valider les notebooks
python scripts/notebook_tools.py validate GenAI --quick
python scripts/notebook_tools.py validate MyIA.AI.Notebooks/ML --quick

# Exécuter en batch
python scripts/notebook_tools.py execute GenAI --timeout 300
```

### Support
- Issues GitHub: Bugs et demandes
- Discord: Communauté étudiante
- Wiki: Documentation détaillée

---
*Créé avec ❤️ par l'équipe CoursIA | Architecture SDDD | Compatible MCP*
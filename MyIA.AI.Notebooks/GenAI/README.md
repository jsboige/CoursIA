# GenAI - Ecosysteme IA Generative

Ecosysteme modulaire de generation de contenu par Intelligence Artificielle : images, texte, agents et vibe-coding.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 96 |
| Sous-domaines | 8 (Environment, Image, Audio, Video, Texte, SemanticKernel, EPF, Vibe-Coding) |
| Duree totale | ~60-70h |
| Taux validation | 95%+ |

## Structure

```
GenAI/
├── 00-GenAI-Environment/    # Setup et configuration (6 notebooks)
├── Image/                   # Generation d'images (19 notebooks)
├── Audio/                   # Speech, TTS, musique, separation (16 notebooks)
├── Video/                   # Generation et comprehension video (16 notebooks)
├── Texte/                   # LLMs et generation de texte (10 notebooks)
├── SemanticKernel/          # Microsoft Semantic Kernel (14 notebooks)
├── EPF/                     # Projets etudiants (4 notebooks)
└── Vibe-Coding/             # Tutorials Claude Code et Roo Code
```

## Sous-domaines

### 00-GenAI-Environment - Setup et Infrastructure
*Niveau Debutant | Prerequis obligatoires*
*Validation: 100% (6/6 notebooks)*

| Notebook | Description | Technologies |
|----------|-------------|--------------|
| **00-1-Environment-Setup** | Configuration environnement complet | Python, Docker, API Keys |
| **00-2-Docker-Services-Management** | Gestion services conteneurisés | Docker Compose, Portainer |
| **00-3-API-Endpoints-Configuration** | Configuration endpoints API | OpenAI, Hugging Face, Local |
| **00-4-Environment-Validation** | Tests et validation setup | Pytest, Monitoring |
| **00-5-ComfyUI-Local-Test** | Test local des services ComfyUI | ComfyUI, Bearer Token |
| **00-6-Local-Docker-Deployment** | Deploiement Docker local complet | Docker Compose, GPU |

### 🖼️ **01-Images-Foundation** (Modèles Base)
*🟢 Niveau Débutant | Introduction aux fondamentaux*
*Validation: 100% (5/5 notebooks)*

| Notebook | Description | Technologies |
|----------|-------------|--------------|
| **01-1-OpenAI-DALL-E-3** | Génération images DALL-E 3 | OpenAI API, PIL, Prompting |
| **01-2-GPT-5-Image-Generation** | GPT-5 pour création visuelle | GPT-5 API, Vision multimodale |
| **01-3-Basic-Image-Operations** | Opérations images de base | PIL, OpenCV, Transforms |

### 🎨 **02-Images-Advanced** (Techniques Avancées)
*🟠 Niveau Intermédiaire | Modèles spécialisés*
*Validation: 100% (4/4 notebooks)*

| Notebook | Description | Technologies |
|----------|-------------|--------------|
| **02-1-Qwen-Image-Edit-2509** | Édition avancée Qwen 2.5 | Qwen API, InPainting |
| **02-2-FLUX-1-Advanced-Generation** | Génération haute qualité FLUX | FLUX.1, LoRA, Fine-tuning |
| **02-3-Stable-Diffusion-3-5** | Stable Diffusion production | SD 3.5, ControlNet, Custom |
| **02-4-Z-Image-Lumina2** | Génération Z-Image (Lumina-2) | ComfyUI, Gemma-2, WanVAE |

### 🔄 **03-Images-Orchestration** (Multi-Modèles)
*🔴 Niveau Expert | Orchestration complexe*
*Validation: 100% (3/3 notebooks)*

| Notebook | Description | Technologies |
|----------|-------------|--------------|
| **03-1-Multi-Model-Comparison** | Comparaison performances | Benchmarking, Métriques |
| **03-2-Workflow-Orchestration** | Chaînage modèles complexes | Langchain, Workflows |
| **03-3-Performance-Optimization** | Optimisation et scaling | Caching, Load Balancing |

### 🏗️ **04-Images-Applications** (Applications Métier)
*🔴 Niveau Expert | Cas d'usage production*
*Validation: 100% (4/4 notebooks)*

| Notebook | Description | Technologies |
|----------|-------------|--------------|
| **04-1-Educational-Content-Generation** | Contenu éducatif automatisé | Curriculum, Adaptive Learning |
| **04-2-Creative-Workflows** | Workflows créatifs avancés | Design Systems, Branding |
| **04-3-Production-Integration** | Intégration systèmes production | APIs, Microservices |
| **04-3-Cross-Stitch-Pattern-Maker-Legacy** | Générateur motifs point de croix | DMC Colors, Pattern Generation |

### Audio/ - Speech, Voix & Musique par IA

*Serie complete pour le traitement audio par IA generative (16 notebooks)*
*Validation: 100% (16/16 notebooks)*

| Niveau | Notebooks | Contenu |
|--------|-----------|---------|
| **Foundation** | 01-1 a 01-5 | OpenAI TTS, Whisper STT, operations audio, Whisper local, Kokoro TTS |
| **Advanced** | 02-1 a 02-4 | Chatterbox TTS, XTTS voice cloning, MusicGen, Demucs separation |
| **Orchestration** | 03-1 a 03-3 | Multi-model comparison, pipelines, temps reel |
| **Applications** | 04-1 a 04-4 | Contenu educatif, transcription, composition musicale, sync A/V |

[README Audio](Audio/README.md)

### Video/ - Generation & Comprehension Video par IA

*Serie complete pour la generation et comprehension video par IA (16 notebooks)*
*Validation: 100% (16/16 notebooks)*

| Niveau | Notebooks | Contenu |
|--------|-----------|---------|
| **Foundation** | 01-1 a 01-5 | Operations video, GPT-5 understanding, Qwen-VL, ESRGAN, AnimateDiff |
| **Advanced** | 02-1 a 02-4 | HunyuanVideo, LTX-Video, Wan, SVD image-to-video |
| **Orchestration** | 03-1 a 03-3 | Multi-model comparison, workflows, ComfyUI Video |
| **Applications** | 04-1 a 04-4 | Video educative, workflows creatifs, Sora API, production |

[README Video](Video/README.md)

### Texte/ - Generation de Texte par IA

*Serie complete sur les LLMs et APIs OpenAI modernes (10 notebooks)*
*Validation: 100% (10/10 notebooks)*

| Tier | Notebooks | Contenu |
|------|-----------|---------|
| **Fondations** | 1-2 | OpenAI Intro, Prompt Engineering |
| **Sorties Structurees** | 3-4 | Structured Outputs, Function Calling |
| **Augmentation** | 5-7 | RAG moderne, PDF/Web Search, Code Interpreter |
| **Avance** | 8-10 | Reasoning Models, Production Patterns, Local LLMs |

[README Texte](Texte/README.md)

### SemanticKernel/ - Microsoft Semantic Kernel

*SDK pour integration LLMs dans applications .NET/Python (20 notebooks)*
*Validation: 85% (17/20 notebooks)*

| Section | Notebooks | Contenu |
|---------|-----------|---------|
| **Serie principale** | 01-08 | Fundamentals, Functions, Agents, Filters, VectorStores, Process, MultiModal, MCP |
| **Interop avancee** | 09-10 | Python/C# CLR, NotebookMaker (3 variantes) |
| **Templates** | 3 | Templates C# et Python |

[README SemanticKernel](SemanticKernel/README.md)

### EPF/ - Projets Etudiants

*Projets realises par les etudiants EPF (4 notebooks)*

| Projet | Auteurs | Description |
|--------|---------|-------------|
| barbie-schreck | Carole & Cleo | Generation images style Barbie/Shrek |
| receipe_maker | Dorian & Bastien | Generateur de recettes |
| medical_chatbot | Louise & Jeanne Celine | Chatbot medical educatif |
| fort-boyard-python | - | Challenges style Fort Boyard |

[README EPF](EPF/README.md)

### Vibe-Coding/ - Tutorials IA Generative pour Developpeurs

*Ateliers Claude Code et Roo Code*

| Section | Contenu | Duree |
|---------|---------|-------|
| Claude-Code | 5 modules (decouverte a automatisation) | 13-16h |
| Roo-Code | 5 modules + ateliers avances | ~15h |

[README Vibe-Coding](Vibe-Coding/README.md)

---

## Liens vers sous-README

| Sous-domaine | README |
|--------------|--------|
| Image | [Image/README.md](Image/README.md) |
| Audio | [Audio/README.md](Audio/README.md) |
| Video | [Video/README.md](Video/README.md) |
| Texte | [Texte/README.md](Texte/README.md) |
| SemanticKernel | [SemanticKernel/README.md](SemanticKernel/README.md) |
| EPF | [EPF/README.md](EPF/README.md) |
| Vibe-Coding | [Vibe-Coding/README.md](Vibe-Coding/README.md) |

---

## Statut des Modules

| Module | Statut | Validation | Description |
|--------|--------|------------|-------------|
| 00-GenAI-Environment | Complet | 100% (6/6) | Setup et configuration |
| 01-Images-Foundation | Complet | 100% (5/5) | DALL-E 3, GPT-5, Forge, Qwen |
| 02-Images-Advanced | Complet | 100% (4/4) | Qwen 2509, FLUX, SD 3.5, Z-Image |
| 03-Images-Orchestration | Complet | 100% (3/3) | Comparaison, Workflows, Optimisation |
| 04-Images-Applications | Complet | 100% (4/4) | Applications pedagogiques |
| Audio/ | Complet | 100% (16/16) | 16 notebooks : TTS, STT, voix, musique, separation |
| Video/ | Complet | 100% (16/16) | 16 notebooks : Operations, comprehension, generation, workflows |
| Texte/ | Complet | 100% (10/10) | 10 notebooks : OpenAI, Prompts, Structured Outputs, RAG, Reasoning, Production |
| SemanticKernel/ | Complet | 85% (17/20) | SDK Microsoft pour integration LLMs |

---

## 🚀 **Demarrage Rapide**

### 1. **Prérequis**
```bash
# Cloner le projet CoursIA
cd MyIA.AI.Notebooks/GenAI

# Configuration environnement
cp .env.example .env
# Éditer .env avec vos API keys (token fourni par l'enseignant pour le cours)
```

### 2. **Installation**
```bash
# Installation dépendances Python
pip install -r requirements.txt

# Validation environment (MCP)
python -c "import jupyter_client; print('✅ Jupyter OK')"
```

### 3. **Première Exécution**
```bash
# Lancer Jupyter Lab
jupyter lab

# Commencer par 00-GenAI-Environment/
# Ordre recommandé : 00-1 → 00-2 → 00-3 → 00-4
```

---

## 🔐 **Authentification ComfyUI**

> **NOUVEAU** : L'accès à ComfyUI nécessite désormais une authentification Bearer Token pour sécuriser les services GenAI.

### 📋 **Guide Rapide Étudiants**

1. **Obtenir votre token** : Contactez votre enseignant pour recevoir votre token personnel Bearer
2. **Configuration** : Créez un fichier `.env` dans `MyIA.AI.Notebooks/GenAI/`
3. **Utilisation** : Les notebooks chargent automatiquement les credentials

📖 **Documentation complète** :
- **Guide Étudiants** : [`README-ETUDIANTS-AUTH.md`](README-ETUDIANTS-AUTH.md) - Configuration pas-à-pas
- **Documentation Technique** : [`README-AUTH.md`](README-AUTH.md) - Architecture d'authentification
- **Scripts Admin** : [`scripts/genai-auth/`](../../scripts/genai-auth/) - Gestion des tokens

### ⚠️ **Important**
- ✅ Tous les notebooks supportent l'authentification (graceful degradation si désactivée)
- ✅ Helper Python : `comfyui_client.py` gère automatiquement les credentials
- ⚠️ Ne partagez JAMAIS votre token - il est personnel et traçable

---

## ⚙️ **Configuration**

### 🔑 **Variables Environnement** (`.env`)
```bash
# Authentification ComfyUI (REQUIS pour services locaux)
COMFYUI_BASE_URL=http://localhost:8188
COMFYUI_BEARER_TOKEN=YOUR_TOKEN_HERE    # Token fourni par l'enseignant

# APIs Principales
OPENAI_API_KEY=sk-...              # DALL-E 3, GPT-5
ANTHROPIC_API_KEY=sk-ant-...       # Claude Vision
HUGGINGFACE_TOKEN=hf_...           # Modèles HF

# Services Locaux
DOCKER_HOST=localhost:2376         # Docker Services
JUPYTER_TOKEN=your-secure-token    # Jupyter Security

# Modèles Spécialisés
QWEN_API_ENDPOINT=https://...      # Qwen 2.5 Image Edit
FLUX_MODEL_PATH=/models/flux/      # FLUX.1 Local
SD35_CHECKPOINT=/models/sd35/      # Stable Diffusion 3.5
```

**Modèle de configuration** : Voir [`.env.example`](.env.example) pour un template complet

### 📦 **Dépendances Principales**
```text
# IA & ML Core
torch>=2.0.0
transformers>=4.35.0
diffusers>=0.24.0
accelerate>=0.24.0

# Image Processing
Pillow>=10.0.0
opencv-python>=4.8.0
numpy>=1.24.0

# Audio Processing
librosa>=0.10.0
soundfile>=0.12.0
pydub>=0.25.0
faster-whisper>=0.10.0

# Video Processing
moviepy>=2.0.0
imageio>=2.31.0
imageio-ffmpeg>=0.4.9
decord>=0.6.0

# Jupyter & Notebooks
jupyter>=1.0.0
ipywidgets>=8.0.0
matplotlib>=3.7.0

# APIs & Clients
openai>=1.3.0
anthropic>=0.7.0
huggingface-hub>=0.19.0
```

### 🎬 **FFmpeg Installation (Requis pour Video/Audio)**

FFmpeg est indispensable pour les notebooks Video et certains notebooks Audio. Il permet :
- **Decodage video** : lecture, conversion, extraction de metadonnees
- **Operations audio** : decoupage, mixing, format conversion
- **Integration Python** : moviepy, pydub, ffmpeg-python

#### Installation Windows

```powershell
# Option 1: Script automatique (recommande)
powershell -ExecutionPolicy Bypass -File scripts/install-ffmpeg.ps1

# Option 2: Installation manuelle winget
winget install FFmpeg

# Option 3: Installation locale (pour developpement)
# Le script installera dans: D:\Dev\CoursIA\tools\ffmpeg\
# Le notebook execution script l'ajoutera automatiquement au PATH
```

#### Installation Linux

```bash
# Ubuntu/Debian
sudo apt update && sudo apt install -y ffmpeg

# Fedora
sudo dnf install -y ffmpeg

# Verifier l'installation
ffmpeg -version
```

#### Installation macOS

```bash
# Via Homebrew
brew install ffmpeg

# Verifier l'installation
ffmpeg -version
```

#### Verification dans Python

```python
# Tester FFmpeg depuis Python
import subprocess
result = subprocess.run(['ffmpeg', '-version'], capture_output=True, text=True)
print(result.stdout.split('\n')[0])  # Affiche la version
```

**Note** : Le script `scripts/genai-stack/commands/notebooks.py` ajoute automatiquement
`D:/Dev/CoursIA/tools/ffmpeg/bin` au PATH lors de l'execution des notebooks.

---

## 📊 **Progression Pédagogique**

### 🎯 **Parcours Recommandés**

#### **👨‍🎓 Débutant (30h)**
1. `00-GenAI-Environment/` - Setup complet (4h)
2. `01-Images-Foundation/` - Bases DALL-E & GPT-5 (8h)
3. `Audio/01-Foundation/` - TTS & STT basics (6h)
4. `Video/01-Foundation/` - Operations video basics (6h)
5. Premier projet pratique (6h)

#### **👨‍💻 Intermédiaire (60h)**
1. Révision Débutant (6h)
2. `02-Images-Advanced/` - Modèles spécialisés (16h)
3. `Audio/02-Advanced/` - Voix, musique, separation (10h)
4. `Video/02-Advanced/` - Generation video (12h)
5. Projet intégration multi-modales (16h)

#### **🚀 Expert (120h)**
1. Révision Intermédiaire (12h)
2. `03-Images-Orchestration/` - Architecture complexe (16h)
3. `Audio/03-Orchestration/` + `04-Applications/` - Pipelines audio (14h)
4. `Video/03-Orchestration/` + `04-Applications/` - Workflows video (16h)
5. `04-Images-Applications/` - Production (20h)
6. Projet production complet (42h)

---

## 🔧 **Outils & Scripts**

### 📜 **Scripts PowerShell**
```powershell
# Génération structure
.\scripts\34-implement-genai-phase2-structure-20251008.ps1

# Création notebooks templates
.\scripts\36-generate-remaining-genai-notebooks-fixed-20251008.ps1

# Correction encodage UTF-8
.\scripts\38-execute-bom-fix-20251008.ps1
```

### 🔍 **Outils Validation**
- **Tests MCP** : Compatibilité infrastructure notebooks
- **Validation JSON** : Conformité notebooks Jupyter
- **Tests API** : Vérification endpoints disponibles

---

## 📚 **Ressources Complémentaires**

### 🎨 **Assets & Données**
- `assets/models/DMC_colors.json` - Palette couleurs point de croix
- `assets/images/` - Images référence et exemples
- `shared/` - Utilitaires Python partagés

### 📖 **Documentation**
- [Architecture Complète](../../docs/genai-image-architecture.md)
- [Templates Phase 2](../../docs/genai-phase2-templates.md)  
- [Standards Développement](../../docs/genai-images-development-standards.md)
- [Guide Déploiement](../../docs/genai-deployment-production-ready.md)

### 🔗 **Intégrations**
- **MCP Jupyter** : Exécution notebooks automatisée
- **Docker Compose** : Services conteneurisés
- **GitHub Actions** : CI/CD notebooks
- **Monitoring** : Métriques production

---

## ⚡ **Performance & Scaling**

### 🚀 **Optimisations**
- **Caching intelligent** : Modèles et résultats
- **Load balancing** : Distribution requêtes API
- **Batch processing** : Traitement lots images
- **GPU acceleration** : CUDA, ROCm, MPS support

### 📈 **Métriques Clés**
- **Latence génération** : <3s DALL-E, <10s SD3.5
- **Qualité output** : FID score, CLIP score
- **Coût par image** : Optimisation budget API
- **Throughput** : Images/heure en production

---

## 🛠️ **Support & Maintenance**

### 🔧 **Dépannage**
1. **Problème API** → Vérifier `.env` et quotas
2. **Erreur Jupyter** → Relancer MCP servers
3. **Memory issues** → Ajuster batch sizes
4. **Model loading** → Vérifier paths modèles

### 📞 **Support**
- **Issues GitHub** : Bugs et demandes fonctionnalités  
- **Discussions** : Questions communauté
- **Documentation** : Wiki complet
- **Examples** : Cas d'usage étendus

---

## 🏆 **Résultats Attendus**

Après completion de cet écosystème, vous maîtriserez :

### 🎯 **Compétences Techniques**
- ✅ **Multi-modal AI** : Texte → Image, Audio, Video
- ✅ **Model comparison** : Évaluation objective performances
- ✅ **Production deployment** : Architecture scalable
- ✅ **Workflow automation** : Chaînes traitement complexes
- ✅ **Speech processing** : STT, TTS, voice cloning, musique
- ✅ **Video understanding** : Compréhension, génération, édition

### 🚀 **Projets Réalisables**
- 🎨 **Générateur contenu visuel** automatisé
- 🎙️ **Podcast/TTS generator** avec voix personnalisées
- 🎬 **Video pédagogique** generée automatiquement
- 📚 **Plateforme éducative** avec contenus multimédia adaptatifs
- 🏭 **Service production** génération à la demande
- 🔬 **Benchmark suite** comparaison modèles multi-modaux

---

**🎓 Bon apprentissage avec l'écosystème GenAI CoursIA !**

*Créé avec ❤️ par l'équipe CoursIA | Architecture SDDD | Compatible MCP*
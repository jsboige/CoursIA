# GenAI - Ecosysteme IA Generative

Ecosysteme modulaire de generation de contenu par Intelligence Artificielle : images, texte, agents et vibe-coding.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 50+ |
| Sous-domaines | 6 (Environment, Image, Texte, SemanticKernel, EPF, Vibe-Coding) |
| Duree totale | ~25-30h |

## Structure

```
GenAI/
├── 00-GenAI-Environment/    # Setup et configuration (5 notebooks)
├── Image/                   # Generation d'images (19 notebooks)
├── Texte/                   # LLMs et texte (4 notebooks)
├── SemanticKernel/          # Microsoft Semantic Kernel (15 notebooks)
├── EPF/                     # Projets etudiants (4 notebooks)
└── Vibe-Coding/             # Tutorials Claude Code et Roo Code
```

## Sous-domaines

### 00-GenAI-Environment - Setup et Infrastructure
*Niveau Debutant | Prerequis obligatoires*

| Notebook | Description | Technologies |
|----------|-------------|--------------|
| **00-1-Environment-Setup** | Configuration environnement complet | Python, Docker, API Keys |
| **00-2-Docker-Services-Management** | Gestion services conteneurisés | Docker Compose, Portainer |
| **00-3-API-Endpoints-Configuration** | Configuration endpoints API | OpenAI, Hugging Face, Local |
| **00-4-Environment-Validation** | Tests et validation setup | Pytest, Monitoring |

### 🖼️ **01-Images-Foundation** (Modèles Base)
*🟢 Niveau Débutant | Introduction aux fondamentaux*

| Notebook | Description | Technologies |
|----------|-------------|--------------|
| **01-1-OpenAI-DALL-E-3** | Génération images DALL-E 3 | OpenAI API, PIL, Prompting |
| **01-2-GPT-5-Image-Generation** | GPT-5 pour création visuelle | GPT-5 API, Vision multimodale |
| **01-3-Basic-Image-Operations** | Opérations images de base | PIL, OpenCV, Transforms |

### 🎨 **02-Images-Advanced** (Techniques Avancées)
*🟠 Niveau Intermédiaire | Modèles spécialisés*

| Notebook | Description | Technologies |
|----------|-------------|--------------|
| **02-1-Qwen-Image-Edit-2509** | Édition avancée Qwen 2.5 | Qwen API, InPainting |
| **02-2-FLUX-1-Advanced-Generation** | Génération haute qualité FLUX | FLUX.1, LoRA, Fine-tuning |
| **02-3-Stable-Diffusion-3-5** | Stable Diffusion production | SD 3.5, ControlNet, Custom |
| **02-4-Z-Image-Lumina2** | Génération Z-Image (Lumina-2) | ComfyUI, Gemma-2, WanVAE |

### 🔄 **03-Images-Orchestration** (Multi-Modèles)
*🔴 Niveau Expert | Orchestration complexe*

| Notebook | Description | Technologies |
|----------|-------------|--------------|
| **03-1-Multi-Model-Comparison** | Comparaison performances | Benchmarking, Métriques |
| **03-2-Workflow-Orchestration** | Chaînage modèles complexes | Langchain, Workflows |
| **03-3-Performance-Optimization** | Optimisation et scaling | Caching, Load Balancing |

### 🏗️ **04-Images-Applications** (Applications Métier)
*🔴 Niveau Expert | Cas d'usage production*

| Notebook | Description | Technologies |
|----------|-------------|--------------|
| **04-1-Educational-Content-Generation** | Contenu éducatif automatisé | Curriculum, Adaptive Learning |
| **04-2-Creative-Workflows** | Workflows créatifs avancés | Design Systems, Branding |
| **04-3-Production-Integration** | Intégration systèmes production | APIs, Microservices |
| **04-3-Cross-Stitch-Pattern-Maker-Legacy** | Générateur motifs point de croix | DMC Colors, Pattern Generation |

### Texte/ - Generation de Texte

*Complementaire aux modules Images*

| Notebook | Description | Technologies |
|----------|-------------|--------------|
| **1_OpenAI_Intro** | Introduction a l'API OpenAI | GPT-4, Chat Completions |
| **2_PromptEngineering** | Techniques de prompt engineering | Few-shot, Chain-of-Thought |
| **3_RAG** | Retrieval Augmented Generation | Embeddings, Vector Search |
| **4_LocalLlama** | Utilisation de LLMs locaux | Llama, Ollama |

[README Texte](Texte/README.md)

### SemanticKernel/ - Microsoft Semantic Kernel

*SDK pour integration LLMs dans applications .NET/Python*

| Notebook | Description |
|----------|-------------|
| **01-SemanticKernel-Intro** | Introduction, setup, premiers plugins |
| **02-SemanticKernel-Advanced** | Plugins avances, chaining |
| **03-SemanticKernel-Agents** | Agents autonomes |
| **05-SemanticKernel-NotebookMaker** | Generation automatique de notebooks |

[README SemanticKernel](SemanticKernel/README.md)

### EPF/ - Projets Etudiants

*Projets realises par les etudiants EPF*

| Projet | Auteurs | Description |
|--------|---------|-------------|
| barbie-schreck | Carole & Cleo | Generation images style Barbie/Shrek |
| receipe_maker | Dorian & Bastien | Generateur de recettes |
| medical_chatbot | Louise & Jeanne Celine | Chatbot medical educatif |

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
| Texte | [Texte/README.md](Texte/README.md) |
| SemanticKernel | [SemanticKernel/README.md](SemanticKernel/README.md) |
| EPF | [EPF/README.md](EPF/README.md) |
| Vibe-Coding | [Vibe-Coding/README.md](Vibe-Coding/README.md) |

---

## Statut des Modules

| Module | Statut | Description |
|--------|--------|-------------|
| 00-GenAI-Environment | Complet | Setup et configuration |
| 01-Images-Foundation | Complet | DALL-E 3, GPT-5, Forge, Qwen |
| 02-Images-Advanced | Complet | Qwen 2509, FLUX, SD 3.5, Z-Image |
| 03-Images-Orchestration | Complet | Comparaison, Workflows, Optimisation |
| 04-Images-Applications | Complet | Applications pedagogiques |
| Texte/ | Reference | OpenAI Intro, Prompts, RAG, Local LLMs |

---

## 🚀 **Demarrage Rapide**

### 1. **Prérequis**
```bash
# Cloner le projet CoursIA
cd MyIA.AI.Notebooks/GenAI

# Configuration environnement
cp .env.template .env
# Éditer .env avec vos API keys
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

# Jupyter & Notebooks
jupyter>=1.0.0
ipywidgets>=8.0.0
matplotlib>=3.7.0

# APIs & Clients
openai>=1.3.0
anthropic>=0.7.0
huggingface-hub>=0.19.0
```

---

## 📊 **Progression Pédagogique**

### 🎯 **Parcours Recommandés**

#### **👨‍🎓 Débutant (20h)**
1. `00-GenAI-Environment/` - Setup complet (4h)
2. `01-Images-Foundation/` - Bases DALL-E & GPT-5 (8h)
3. `01-3-Basic-Image-Operations` - Manipulation images (4h)
4. Premier projet pratique (4h)

#### **👨‍💻 Intermédiaire (40h)**
1. Révision Débutant (4h)
2. `02-Images-Advanced/` - Modèles spécialisés (16h)
3. `03-1-Multi-Model-Comparison` - Évaluation (8h)
4. Projet intégration multi-modèles (12h)

#### **🚀 Expert (80h)**
1. Révision Intermédiaire (8h)
2. `03-Images-Orchestration/` - Architecture complexe (24h)
3. `04-Images-Applications/` - Production (32h)
4. Projet production complet (16h)

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
- ✅ **Multi-modal AI** : Texte → Image, Image → Image
- ✅ **Model comparison** : Évaluation objective performances  
- ✅ **Production deployment** : Architecture scalable
- ✅ **Workflow automation** : Chaînes traitement complexes

### 🚀 **Projets Réalisables**
- 🎨 **Générateur contenu visuel** automatisé
- 📚 **Plateforme éducative** avec images adaptatives
- 🏭 **Service production** génération à la demande
- 🔬 **Benchmark suite** comparaison modèles

---

**🎓 Bon apprentissage avec l'écosystème GenAI Images CoursIA !**

*Créé avec ❤️ par l'équipe CoursIA | Architecture SDDD | Compatible MCP*
# 📑 INDEX COMPLET - GenAI Images Ecosystem CoursIA

> **Guide de navigation complet de l'écosystème GenAI Images**  
> Production-ready | 18 Notebooks | APIs Externes | Documentation Complète

---

## 📖 Table des Matières

1. [Vue d'Ensemble](#vue-densemble)
2. [Quick Start](#quick-start)
3. [Structure Modulaire](#structure-modulaire)
4. [Notebooks par Niveau](#notebooks-par-niveau)
5. [Tutoriels et Guides](#tutoriels-et-guides)
6. [Exemples Sectoriels](#exemples-sectoriels)
7. [Matrice Fonctionnalités](#matrice-fonctionnalités)
8. [Parcours d'Apprentissage](#parcours-dapprentissage)
9. [Configuration et Prérequis](#configuration-et-prérequis)
10. [APIs et Intégrations](#apis-et-intégrations)
11. [Documentation Technique](#documentation-technique)
12. [Troubleshooting](#troubleshooting)
13. [FAQ](#faq)

---

## 🎯 Vue d'Ensemble

### Description

L'écosystème **GenAI Images CoursIA** est une plateforme modulaire complète pour la **génération, l'édition et l'analyse d'images par Intelligence Artificielle** dans un contexte pédagogique. Conçu selon les principes **SDDD (Semantic-Documentation-Driven-Design)** et compatible avec l'infrastructure **MCP (MyIA Control Plane)**.

### Objectifs

- ✅ **Formation progressive** : Du débutant à l'expert en 4 niveaux
- ✅ **Production-ready** : Applications déployables immédiatement
- ✅ **Multi-modèles** : DALL-E 3, GPT-5, Qwen, FLUX, SD 3.5
- ✅ **Pédagogique** : Cas d'usage éducatifs concrets
- ✅ **Scalable** : Architecture modulaire extensible

### Statistiques

| Métrique | Valeur |
|----------|--------|
| **Notebooks totaux** | 18 |
| **Tutoriels complets** | 4 (8500+ lignes) |
| **Exemples sectoriels** | 4 domaines |
| **APIs configurées** | 3 (OpenAI, OpenRouter, GPT-5) |
| **Niveaux formation** | 4 (00-04) |
| **Documentation** | 15+ documents |

---

## 🚀 Quick Start

### Installation Rapide (5 minutes)

```bash
# 1. Cloner le projet
cd MyIA.AI.Notebooks/GenAI

# 2. Configuration environnement
python -m venv venv
source venv/bin/activate  # Windows: venv\Scripts\activate
pip install -r requirements.txt

# 3. Configuration clés API (.env)
cp .env.example .env
# Éditer .env avec vos clés API

# 4. Validation installation
jupyter notebook 00-GenAI-Environment/00-4-Environment-Validation.ipynb
```

### Premier Notebook (10 minutes)

```python
# Génération image simple avec DALL-E 3
from openai import OpenAI
import os

client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

response = client.images.generate(
    model="dall-e-3",
    prompt="Illustration pédagogique cellule végétale, labels français",
    size="1024x1024",
    quality="standard"
)

print(f"✅ Image générée: {response.data[0].url}")
```

### Notebooks Recommandés pour Démarrer

1. **00-1-Environment-Setup** : Configuration complète
2. **01-1-OpenAI-DALL-E-3** : Premier modèle génération
3. **01-2-GPT-5-Image-Generation** : Analyse multimodale
4. **04-1-Educational-Content-Generation** : Application pratique

---

## 📂 Structure Modulaire

### Organisation par Niveaux

```
MyIA.AI.Notebooks/GenAI/
│
├── 00-GenAI-Environment/          # 🟢 Setup & Configuration
│   ├── 00-1-Environment-Setup.ipynb
│   ├── 00-2-Docker-Services-Management.ipynb
│   ├── 00-3-API-Endpoints-Configuration.ipynb
│   └── 00-4-Environment-Validation.ipynb
│
├── 01-Images-Foundation/          # 🟢 Fondamentaux
│   ├── 01-1-OpenAI-DALL-E-3.ipynb
│   ├── 01-2-GPT-5-Image-Generation.ipynb
│   └── 01-3-Basic-Image-Operations.ipynb
│
├── 02-Images-Advanced/            # 🟠 Avancé (Docker)
│   ├── 02-1-Qwen-Image-Edit-2509.ipynb
│   ├── 02-2-FLUX-1-Advanced-Generation.ipynb
│   └── 02-3-Stable-Diffusion-3-5.ipynb
│
├── 03-Images-Orchestration/       # 🔴 Orchestration (Docker)
│   ├── 03-1-Multi-Model-Comparison.ipynb
│   ├── 03-2-Workflow-Orchestration.ipynb
│   └── 03-3-Performance-Optimization.ipynb
│
├── 04-Images-Applications/        # 🔴 Applications Métier
│   ├── 04-1-Educational-Content-Generation.ipynb
│   ├── 04-2-Creative-Workflows.ipynb
│   └── 04-3-Production-Integration.ipynb
│
├── tutorials/                     # 📚 Guides Complets
│   ├── dalle3-complete-guide.md
│   ├── gpt5-image-analysis-guide.md
│   ├── openrouter-ecosystem-guide.md
│   └── educational-workflows.md
│
├── examples/                      # 🎯 Exemples Sectoriels
│   ├── science-diagrams.ipynb
│   ├── history-geography.ipynb
│   ├── literature-visual.ipynb
│   └── mathematics-physics.ipynb
│
└── docs/                          # 📖 Documentation Technique
    ├── architecture.md
    ├── deployment-guide.md
    ├── development-standards.md
    └── integration-procedures.md
```

---

## 📊 Notebooks par Niveau

### 🟢 Niveau 00 : Environment & Setup (Prérequis)

| Notebook | Temps | Prérequis | Objectifs |
|----------|-------|-----------|-----------|
| **00-1-Environment-Setup** | 30min | Python 3.10+ | Installation complète environnement |
| **00-2-Docker-Services-Management** | 20min | Docker Desktop | Gestion services conteneurisés |
| **00-3-API-Endpoints-Configuration** | 15min | Clés API | Configuration OpenAI, OpenRouter |
| **00-4-Environment-Validation** | 10min | Notebooks 00-1 à 00-3 | Tests validation setup |

**Status APIs Externes** : ✅ Opérationnel  
**Status Docker** : 🚧 En cours (autre agent)

---

### 🟢 Niveau 01 : Images Foundation (Débutant)

| Notebook | Modèle | Temps | Difficulté | Objectifs Clés |
|----------|--------|-------|------------|----------------|
| **01-1-OpenAI-DALL-E-3** | DALL-E 3 | 2h | ⭐ | Génération images haute qualité |
| **01-2-GPT-5-Image-Generation** | GPT-5 Vision | 2h | ⭐ | Analyse multimodale avancée |
| **01-3-Basic-Image-Operations** | PIL/OpenCV | 1h30 | ⭐ | Manipulation images basique |

**Compétences Acquises** :
- ✅ Prompt engineering images
- ✅ APIs OpenAI/OpenRouter
- ✅ Gestion fichiers images Python
- ✅ Cost management de base

---

### 🟠 Niveau 02 : Images Advanced (Intermédiaire)

| Notebook | Modèle | Temps | Difficulté | Prérequis Docker |
|----------|--------|-------|------------|------------------|
| **02-1-Qwen-Image-Edit-2509** | Qwen 2.5 | 3h | ⭐⭐ | ✅ Requis |
| **02-2-FLUX-1-Advanced-Generation** | FLUX.1 | 3h | ⭐⭐ | ✅ Requis |
| **02-3-Stable-Diffusion-3-5** | SD 3.5 | 3h | ⭐⭐ | ✅ Requis |

**Status** : 🚧 Infrastructure Docker en cours de déploiement (agent parallèle)

**Compétences Visées** :
- 🔄 Édition images avancée (inpainting, outpainting)
- 🔄 Fine-tuning modèles
- 🔄 ControlNet et guidage précis
- 🔄 LoRA customization

---

### 🔴 Niveau 03 : Images Orchestration (Avancé)

| Notebook | Focus | Temps | Difficulté | Technologies |
|----------|-------|-------|------------|--------------|
| **03-1-Multi-Model-Comparison** | Benchmarking | 2h | ⭐⭐⭐ | Docker, ComfyUI |
| **03-2-Workflow-Orchestration** | Pipelines | 2h30 | ⭐⭐⭐ | Docker, Async |
| **03-3-Performance-Optimization** | Scaling | 2h | ⭐⭐⭐ | Docker, Queue |

**Status** : 🚧 Infrastructure Docker en cours

**Compétences Visées** :
- 🔄 Comparaison objective modèles
- 🔄 Workflows complexes multi-étapes
- 🔄 Optimisation performance GPU
- 🔄 Production scaling

---

### 🔴 Niveau 04 : Images Applications (Expert)

| Notebook | Application | Temps | Difficulté | Status |
|----------|-------------|-------|------------|--------|
| **04-1-Educational-Content-Generation** | Contenu pédagogique | 3h | ⭐⭐⭐ | ✅ Production |
| **04-2-Creative-Workflows** | Workflows créatifs | 3h | ⭐⭐⭐ | ✅ Production |
| **04-3-Production-Integration** | Intégration systèmes | 2h30 | ⭐⭐⭐ | ✅ Production |

**Status APIs Externes** : ✅ 100% Opérationnel

**Cas d'Usage Concrets** :
- ✅ Génération automatique supports de cours
- ✅ Évaluations visuelles interactives
- ✅ Story-boarding présentations
- ✅ Brand building projets étudiants

---

## 📚 Tutoriels et Guides

### Tutoriels Complets (1000-1600 lignes)

#### 1. **DALL-E 3 Complete Guide** 📘
**Fichier** : [`tutorials/dalle3-complete-guide.md`](tutorials/dalle3-complete-guide.md)  
**Temps lecture** : 30min | **Niveau** : Débutant → Intermédiaire

**Sections Principales** :
- Getting Started avec OpenAI API
- Prompt Engineering pour images
- Variations et éditions avancées
- Intégration workflows CoursIA
- Cas d'usage pédagogiques
- Code examples réutilisables

**Notebooks Associés** :
- `01-1-OpenAI-DALL-E-3.ipynb`
- `04-1-Educational-Content-Generation.ipynb`

---

#### 2. **GPT-5 Image Analysis Guide** 📙
**Fichier** : [`tutorials/gpt5-image-analysis-guide.md`](tutorials/gpt5-image-analysis-guide.md)  
**Temps lecture** : 35min | **Niveau** : Intermédiaire

**Sections Principales** :
- Configuration OpenRouter
- Analyse images et description
- Conversations multimodales avancées
- Templates cas pédagogiques
- Alt text et accessibilité
- Intégration avec DALL-E
- Performance et cost management

**Notebooks Associés** :
- `01-2-GPT-5-Image-Generation.ipynb`
- `04-2-Creative-Workflows.ipynb`

---

#### 3. **OpenRouter Ecosystem Guide** 📗
**Fichier** : [`tutorials/openrouter-ecosystem-guide.md`](tutorials/openrouter-ecosystem-guide.md)  
**Temps lecture** : 40min | **Niveau** : Intermédiaire → Avancé

**Sections Principales** :
- Configuration endpoints multiples
- Switching entre modèles
- Rate limiting et cost optimization
- API management et monitoring
- Error handling et retry strategies
- Production best practices
- Integration patterns CoursIA

**Notebooks Associés** :
- `00-3-API-Endpoints-Configuration.ipynb`
- `04-3-Production-Integration.ipynb`

---

#### 4. **Educational Workflows Tutorial** 📕
**Fichier** : [`tutorials/educational-workflows.md`](tutorials/educational-workflows.md)  
**Temps lecture** : 45min | **Niveau** : Avancé

**Sections Principales** :
- Création automatique supports de cours
- Génération évaluations visuelles
- Story-boarding présentation
- Brand building projets étudiants
- Templates réutilisables par matière
- Quality assurance éducative
- Accessibilité et inclusivité

**Notebooks Associés** :
- `04-1-Educational-Content-Generation.ipynb`
- `04-2-Creative-Workflows.ipynb`

---

## 🎯 Exemples Sectoriels

### Exemples Prêts-à-l'Emploi

#### 1. **Science Diagrams** 🔬
**Fichier** : [`examples/science-diagrams.ipynb`](examples/science-diagrams.ipynb)

**Applications** :
- Diagrammes cellule végétale/animale
- Illustrations photosynthèse
- Schémas anatomie humaine
- Cycles biochimiques
- Expériences scientifiques

**Technologies** : DALL-E 3, GPT-5 Vision, PIL

---

#### 2. **History & Geography** 🗺️
**Fichier** : [`examples/history-geography.ipynb`](examples/history-geography.ipynb)

**Applications** :
- Reconstitutions événements historiques
- Cartes géographiques annotées
- Portraits personnages historiques
- Scènes vie quotidienne périodes
- Évolution paysages

**Technologies** : DALL-E 3, GPT-5 Context

---

#### 3. **Literature & Visual Arts** 📖
**Fichier** : [`examples/literature-visual.ipynb`](examples/literature-visual.ipynb)

**Applications** :
- Illustrations scènes littéraires
- Portraits personnages romans
- Ambiances atmosphériques récits
- Couvertures livres
- Posters promotionnels

**Technologies** : DALL-E 3, Style Transfer

---

#### 4. **Mathematics & Physics** 📐
**Fichier** : [`examples/mathematics-physics.ipynb`](examples/mathematics-physics.ipynb)

**Applications** :
- Diagrammes géométriques annotés
- Graphiques fonctions mathématiques
- Schémas forces physiques
- Représentations 3D solides
- Illustrations concepts abstraits

**Technologies** : DALL-E 3, Matplotlib Integration

---

## 🔧 Matrice Fonctionnalités

### Fonctionnalités par Notebook

| Fonctionnalité | 01-1 | 01-2 | 01-3 | 04-1 | 04-2 | 04-3 |
|----------------|------|------|------|------|------|------|
| **Génération Images** | ✅ | ✅ | ❌ | ✅ | ✅ | ✅ |
| **Analyse Images** | ❌ | ✅ | ✅ | ✅ | ✅ | ❌ |
| **Édition Images** | ❌ | ❌ | ✅ | ❌ | ✅ | ❌ |
| **Batch Processing** | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Cost Tracking** | ✅ | ✅ | ❌ | ✅ | ✅ | ✅ |
| **Quality Validation** | ❌ | ✅ | ❌ | ✅ | ✅ | ✅ |
| **Prompt Engineering** | ✅ | ✅ | ❌ | ✅ | ✅ | ✅ |
| **Multi-Modal** | ❌ | ✅ | ❌ | ✅ | ✅ | ✅ |
| **Production Ready** | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Accessibilité** | ❌ | ✅ | ❌ | ✅ | ✅ | ❌ |

### Technologies par Niveau

| Technologie | Niveau 00 | Niveau 01 | Niveau 02 | Niveau 03 | Niveau 04 |
|-------------|-----------|-----------|-----------|-----------|-----------|
| **OpenAI API** | ✅ | ✅ | ✅ | ✅ | ✅ |
| **OpenRouter** | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Docker** | ✅ | ❌ | ✅ | ✅ | ❌ |
| **PIL/OpenCV** | ❌ | ✅ | ✅ | ✅ | ✅ |
| **Async/Queue** | ❌ | ❌ | ❌ | ✅ | ✅ |
| **MCP Integration** | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Cost Tracking** | ❌ | ✅ | ✅ | ✅ | ✅ |
| **Testing** | ✅ | ✅ | ✅ | ✅ | ✅ |

---

## 🎓 Parcours d'Apprentissage

### Par Profil Utilisateur

#### 👨‍🎓 **Débutant Complet** (20h total)

**Semaine 1-2 : Fondamentaux**
1. `00-1-Environment-Setup` (30min)
2. `00-3-API-Endpoints-Configuration` (15min)
3. `00-4-Environment-Validation` (10min)
4. `01-1-OpenAI-DALL-E-3` (2h)
5. Tutorial : `dalle3-complete-guide.md` (30min)

**Semaine 3-4 : Analyse Multimodale**
6. `01-2-GPT-5-Image-Generation` (2h)
7. Tutorial : `gpt5-image-analysis-guide.md` (35min)
8. `01-3-Basic-Image-Operations` (1h30)

**Semaine 5-6 : Premier Projet**
9. Exemple : `science-diagrams.ipynb` (1h)
10. Projet pratique guidé (4h)

**Compétences Acquises** :
- ✅ Génération images DALL-E 3
- ✅ Analyse images GPT-5
- ✅ Manipulation basique PIL
- ✅ Cost management
- ✅ Premier workflow complet

---

#### 👨‍💼 **Intermédiaire** (30h total)

**Prérequis** : Niveau 01 complété

**Phase 1 : Approfondissement (10h)**
1. Tutorial : `openrouter-ecosystem-guide.md` (40min)
2. Tutorial : `educational-workflows.md` (45min)
3. `04-1-Educational-Content-Generation` (3h)
4. Exemples sectoriels (4h)

**Phase 2 : Applications Pratiques (12h)**
5. `04-2-Creative-Workflows` (3h)
6. `04-3-Production-Integration` (2h30)
7. Projet personnel intermédiaire (6h30)

**Phase 3 : Optimisation (8h)**
8. Cost optimization avancé (2h)
9. Quality assurance workflows (2h)
10. Batch processing at scale (2h)
11. Performance tuning (2h)

**Compétences Acquises** :
- ✅ Workflows complexes multi-étapes
- ✅ Intégration systèmes production
- ✅ Cost optimization avancé
- ✅ Quality validation automatique
- ✅ Accessibilité (WCAG 2.1)

---

#### 🚀 **Expert / Production** (50h total)

**Prérequis** : Niveau 01-04 complétés

**Phase 1 : Docker & Advanced Models (15h)**
1. `00-2-Docker-Services-Management` (20min)
2. `02-1-Qwen-Image-Edit-2509` (3h)
3. `02-2-FLUX-1-Advanced-Generation` (3h)
4. `02-3-Stable-Diffusion-3-5` (3h)
5. Infrastructure Docker setup (5h40)

**Phase 2 : Orchestration (12h)**
6. `03-1-Multi-Model-Comparison` (2h)
7. `03-2-Workflow-Orchestration` (2h30)
8. `03-3-Performance-Optimization` (2h)
9. Benchmarking suite (5h30)

**Phase 3 : Production Deployment (23h)**
10. Architecture scalable design (4h)
11. CI/CD pipelines setup (3h)
12. Monitoring & alerting (3h)
13. Security hardening (2h)
14. Load testing (3h)
15. Projet production complet (8h)

**Compétences Acquises** :
- ✅ Multi-model orchestration
- ✅ Docker production deployment
- ✅ Performance optimization GPU
- ✅ Scalable architecture design
- ✅ CI/CD et DevOps
- ✅ Security best practices

---

#### 👨‍🏫 **Enseignant CoursIA** (Parcours Spécialisé - 15h)

**Focus Pédagogique**

**Module 1 : Génération Contenu (5h)**
1. `01-1-OpenAI-DALL-E-3` (focus prompts éducatifs)
2. Tutorial : `educational-workflows.md`
3. `04-1-Educational-Content-Generation`

**Module 2 : Applications Matières (6h)**
4. `examples/science-diagrams.ipynb`
5. `examples/history-geography.ipynb`
6. `examples/literature-visual.ipynb`
7. `examples/mathematics-physics.ipynb`

**Module 3 : Production Cours (4h)**
8. Templates réutilisables par discipline
9. Batch generation supports complets
10. Quality assurance pédagogique
11. Accessibilité et inclusivité

**Livrables** :
- ✅ Pack visuels pour 1 cours complet
- ✅ Template génération automatique supports
- ✅ Évaluations visuelles interactives
- ✅ Présentation story-boardée

---

## ⚙️ Configuration et Prérequis

### Prérequis Système

#### Matériel Minimum
- **CPU** : Intel i5 / AMD Ryzen 5 (4 cores)
- **RAM** : 8 GB (16 GB recommandé)
- **Stockage** : 10 GB libre
- **Internet** : Connexion stable pour APIs

#### Matériel Recommandé (Niveau 02-03)
- **CPU** : Intel i7 / AMD Ryzen 7 (8 cores)
- **RAM** : 16 GB (32 GB optimal)
- **GPU** : NVIDIA RTX 3060+ (8GB VRAM)
- **Stockage** : 50 GB SSD libre
- **Internet** : Fibre optique

---

### Logiciels Requis

#### Obligatoires (Niveau 00-01, 04)
```bash
# Python
Python 3.10+ (3.11 recommandé)

# Gestionnaire paquets
pip 23.0+

# Jupyter
jupyter-lab 4.0+
jupyter-notebook 7.0+

# Version control
git 2.40+
```

#### Optionnels (Niveau 02-03)
```bash
# Conteneurisation
Docker Desktop 4.20+
Docker Compose 2.18+

# GPU (pour Docker models)
NVIDIA CUDA 12.0+
cuDNN 8.9+
nvidia-docker2
```

---

### Installation Environnement Python

#### Création Environnement Virtuel

```bash
# Création venv
python -m venv genai-env

# Activation
# Windows
genai-env\Scripts\activate

# macOS/Linux
source genai-env/bin/activate

# Upgrade pip
python -m pip install --upgrade pip
```

#### Installation Dépendances

```bash
# Dépendances core
pip install -r requirements.txt

# Vérification installation
python -c "import openai, PIL, requests, jupyter; print('✅ Installation OK')"
```

#### Requirements.txt

```txt
# Core APIs
openai>=1.3.0
anthropic>=0.7.0

# Image processing
Pillow>=10.0.0
opencv-python>=4.8.0
matplotlib>=3.7.0

# Utilities
requests>=2.31.0
python-dotenv>=1.0.0
pyyaml>=6.0

# Jupyter
jupyter>=1.0.0
notebook>=7.0.0
ipykernel>=6.25.0

# Data & Analysis
pandas>=2.1.0
numpy>=1.24.0

# Testing
pytest>=7.4.0
pytest-asyncio>=0.21.0

# Optional (Advanced)
# comfyui-api>=0.1.0
# diffusers>=0.25.0
# transformers>=4.35.0
```

---

## 🔌 APIs et Intégrations

### APIs Configurées

#### 1. **OpenAI API** ✅

**Modèles Disponibles** :
- `dall-e-3` : Génération images haute qualité

**Configuration** :
```python
from openai import OpenAI
import os

client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

# Test connexion
response = client.images.generate(
    model="dall-e-3",
    prompt="Test connection",
    size="1024x1024"
)
print("✅ OpenAI API opérationnelle")
```

**Coûts** :
- Standard (1024x1024) : $0.040/image
- HD (1024x1024) : $0.080/image
- HD (1792x1024) : $0.120/image

**Documentation** :
- [OpenAI Images API](https://platform.openai.com/docs/guides/images)
- Tutorial : [`dalle3-complete-guide.md`](tutorials/dalle3-complete-guide.md)

---

#### 2. **OpenRouter API** ✅

**Modèles Disponibles** :
- `openai/gpt-5-preview` : Vision multimodale
- `openai/gpt-4-turbo` : Texte haute qualité
- `anthropic/claude-3.5-sonnet` : Raisonnement
- `google/gemini-pro-vision` : Vision alternative

**Configuration** :
```python
from openai import OpenAI
import os

client = OpenAI(
    api_key=os.getenv("OPENROUTER_API_KEY"),
    base_url="https://openrouter.ai/api/v1"
)

# Test GPT-5
response = client.chat.completions.create(
    model="openai/gpt-5-preview",
    messages=[{"role": "user", "content": "Test"}]
)
print("✅ OpenRouter API opérationnelle")
```

**Avantages** :
- ✅ Accès 200+ modèles via API unique
- ✅ Rate limiting automatique
- ✅ Cost optimization
- ✅ Fallback models

**Documentation** :
- [OpenRouter Docs](https://openrouter.ai/docs)
- Tutorial : [`openrouter-ecosystem-guide.md`](tutorials/openrouter-ecosystem-guide.md)

---

#### 3. **Configuration .env**

**Template .env.example** :
```bash
# OpenAI (DALL-E 3)
OPENAI_API_KEY=sk-...

# OpenRouter (GPT-5, GPT-4, Claude, Gemini)
OPENROUTER_API_KEY=sk-or-...

# Anthropic (optionnel)
ANTHROPIC_API_KEY=sk-ant-...

# Hugging Face (optionnel)
HUGGINGFACE_TOKEN=hf_...

# Docker Services (niveau 02-03)
# COMFYUI_URL=http://localhost:8188
# QWEN_API_URL=http://localhost:8000
# FLUX_API_URL=http://localhost:8001
# SD35_API_URL=http://localhost:8002
```

**Sécurité Clés API** :
- ⚠️ **JAMAIS** commiter .env dans Git
- ✅ Utiliser `.gitignore` pour exclure .env
- ✅ Rotation régulière clés API
- ✅ Limites budgétaires configurées

---

### Intégrations CoursIA

#### MCP (MyIA Control Plane)

**Compatibilité** : ✅ 100%

**Fonctionnalités MCP** :
- Exécution notebooks via Papermill
- Gestion job queue asynchrone
- Monitoring temps réel
- Logs centralisés

**Exemple Exécution** :
```python
# Via MCP Papermill
from papermill import execute_notebook

execute_notebook(
    '01-1-OpenAI-DALL-E-3.ipynb',
    'output.ipynb',
    parameters={
        'prompt': 'Custom prompt',
        'output_dir': 'outputs/my_project'
    }
)
```

---

## 📖 Documentation Technique

### Documents Disponibles

#### Architecture & Design

1. **[`docs/genai/architecture.md`](../../../docs/suivis/genai-image/architecture.md)**
   - Architecture modulaire complète
   - Diagrammes composants
   - Flux de données
   - Patterns conception

2. **[`docs/genai/development-standards.md`](../../../docs/suivis/genai-image/development-standards.md)**
   - Standards code Python
   - Conventions nommage
   - Structure notebooks
   - Documentation requirements

3. **[`docs/genai/docker-lifecycle-management.md`](../../../docs/suivis/genai-image/docker-lifecycle-management.md)**
   - Cycle de vie containers
   - Orchestration Docker Compose
   - Health checks
   - Logs management

---

#### Déploiement & Production

4. **[`docs/genai/deployment-guide.md`](../../../docs/suivis/genai-image/deployment-guide.md)**
   - Environnements (dev, staging, prod)
   - CI/CD pipelines
   - Monitoring alerting
   - Backup/restore

5. **[`DEPLOYMENT.md`](DEPLOYMENT.md)**
   - Guide déploiement production
   - Security best practices
   - Scaling strategies
   - Cost optimization

6. **[`docs/genai/environment-configurations.md`](../../../docs/suivis/genai-image/environment-configurations.md)**
   - Configuration environnements multiples
   - Variables d'environnement
   - Secrets management
   - Testing configurations

---

#### Testing & Quality

7. **[`docs/genai/infrastructure-tests.md`](../../../docs/suivis/genai-image/infrastructure-tests.md)**
   - Tests unitaires
   - Tests intégration
   - Tests end-to-end
   - Performance benchmarks

8. **[`docs/genai/integration-procedures.md`](../../../docs/suivis/genai-image/integration-procedures.md)**
   - Procédures intégration
   - APIs testing
   - Validation workflows
   - Rollback procedures

---

#### Templates & Guides

9. **[`docs/genai/phase2-templates.md`](../../../docs/suivis/genai-image/phase2-templates.md)**
   - Templates notebooks
   - Boilerplate code
   - Configuration types
   - Patterns réutilisables

10. **[`TROUBLESHOOTING.md`](TROUBLESHOOTING.md)**
    - Résolution problèmes courants
    - Erreurs APIs
    - Issues configuration
    - Scripts diagnostiques

---

## 🔧 Troubleshooting

### Accès Rapide

**Guide Complet** : [`TROUBLESHOOTING.md`](TROUBLESHOOTING.md)

### Problèmes Fréquents

#### 🔴 Erreur API Key Invalid

```python
# Error: openai.AuthenticationError: Invalid API key

# Solution
import os
print(f"API Key: {os.getenv('OPENAI_API_KEY')[:10]}...")

# Vérifier .env existe et est chargé
from dotenv import load_dotenv
load_dotenv()
```

---

#### 🔴 Rate Limit Exceeded

```python
# Error: Rate limit reached for requests

# Solution : Retry avec backoff exponentiel
import time
from openai import RateLimitError

def generate_with_retry(prompt, max_retries=3):
    for attempt in range(max_retries):
        try:
            return client.images.generate(...)
        except RateLimitError:
            wait_time = 2 ** attempt
            print(f"Rate limit, waiting {wait_time}s...")
            time.sleep(wait_time)
    raise Exception("Max retries reached")
```

---

#### 🔴 MCP Papermill BOM UTF-8

```python
# Error: BOM detected in notebook

# Solution : Script automatique
python scripts/37-fix-genai-bom-utf8-20251008.ps1
```

---

#### 🔴 Out of Memory (Images)

```python
# Solution : Libération mémoire
from PIL import Image
import gc

# Après traitement image
del image
gc.collect()

# Ou redimensionnement
img = Image.open('large.png')
img.thumbnail((1024, 1024))
img.save('optimized.png')
```

---

### Support & Communauté

- 📧 **Email** : support@coursia.ai
- 💬 **Discord** : [CoursIA Community](https://discord.gg/coursia)
- 📚 **Docs** : [docs.coursia.ai/genai](https://docs.coursia.ai/genai)
- 🐛 **Issues** : [GitHub Issues](https://github.com/coursia/genai/issues)

---

## ❓ FAQ

### Questions Générales

**Q: Quel est le coût moyen d'utilisation ?**  
**R:** Niveau 01 (APIs externes) : ~$1.50-5/mois pour usage pédagogique typique. Voir cost tracking dans notebooks.

**Q: Puis-je utiliser sans GPU ?**  
**R:** Oui ! Niveaux 00-01 et 04 utilisent APIs externes, pas besoin de GPU. GPU requis uniquement pour niveaux 02-03 (Docker).

**Q: Combien de temps pour devenir opérationnel ?**  
**R:** Configuration initiale : 15min. Premier notebook fonctionnel : 30min supplémentaires.

**Q: Compatible avec Google Colab ?**  
**R:** Oui pour niveaux 00-01, 04. Niveaux 02-03 (Docker) requièrent environnement local.

---

### Questions Techniques

**Q: Quelle résolution maximum pour DALL-E 3 ?**  
**R:** 1792x1024 (landscape) ou 1024x1792 (portrait). Default : 1024x1024 (square).

**Q: GPT-5 supporte combien d'images simultanées ?**  
**R:** Jusqu'à 10 images en contexte unique avec 200K tokens context window.

**Q: Comment optimiser les coûts ?**  
**R:** Voir tutorial [`openrouter-ecosystem-guide.md`](tutorials/openrouter-ecosystem-guide.md) section cost optimization.

**Q: Peut-on fine-tuner DALL-E 3 ?**  
**R:** Non directement, mais techniques prompt engineering très efficaces. Pour fine-tuning custom, voir niveau 02 (FLUX.1, SD 3.5).

---

### Questions Pédagogiques

**Q: Quels sujets couverts ?**  
**R:** Sciences, Histoire, Géographie, Littérature, Mathématiques, Physique. Voir [`examples/`](examples/).

**Q: Accessibilité pour élèves handicapés ?**  
**R:** Oui, génération automatique alt-text via GPT-5. Voir tutorial [`educational-workflows.md`](tutorials/educational-workflows.md).

**Q: Peut-on générer QCM automatiquement ?**  
**R:** Oui ! Voir `04-1-Educational-Content-Generation.ipynb` section "Visual Assessments".

**Q: Intégration Moodle/Canvas ?**  
**R:** Exportation formats standards (SCORM, QTI). Voir `04-3-Production-Integration.ipynb`.

---

## 🚀 Prochaines Étapes

### Démarrage Immédiat

1. **Configuration** : Suivre [Quick Start](#quick-start)
2. **Premier Notebook** : `01-1-OpenAI-DALL-E-3.ipynb`
3. **Tutorial** : Lire [`dalle3-complete-guide.md`](tutorials/dalle3-complete-guide.md)
4. **Exemple** : Exécuter [`examples/science-diagrams.ipynb`](examples/science-diagrams.ipynb)

### Parcours Recommandé

**Semaine 1** : Niveau 00 + 01  
**Semaine 2** : Tutorials + Exemples  
**Semaine 3** : Niveau 04 Applications  
**Semaine 4** : Projet personnel

### Ressources Complémentaires

- 📚 [Documentation OpenAI](https://platform.openai.com/docs)
- 📚 [OpenRouter Docs](https://openrouter.ai/docs)
- 📺 [CoursIA YouTube](https://youtube.com/@coursia)
- 💬 [Community Discord](https://discord.gg/coursia)

---

## 📞 Contact & Support

### Équipe CoursIA

- 👨‍💻 **Development** : dev@coursia.ai
- 👨‍🏫 **Pédagogie** : pedagogy@coursia.ai
- 🛠️ **Support Technique** : support@coursia.ai

### Contributions

Contributions welcomes ! Voir [`CONTRIBUTING.md`](../../CONTRIBUTING.md)

---

---

## Playwright-OWUI - Tests E2E sur Open WebUI

Serie pedagogique pour apprendre Playwright en testant une application GenAI reelle.

| Module | Nom | Duree | Niveau | Tests |
|--------|-----|-------|--------|-------|
| 01 | [Decouverte](Playwright-OWUI/01-decouverte/) | 2-3h | Debutant | 4 |
| 02 | [Navigation & Auth](Playwright-OWUI/02-navigation-authentification/) | 2-3h | Debutant+ | 8 |
| 03 | [Chat & Streaming](Playwright-OWUI/03-chat-streaming/) | 3h | Intermediaire | 7 |
| 04 | [RAG, MCP & Avances](Playwright-OWUI/04-rag-tools-avances/) | 3h | Intermediaire+ | 7 |
| 05 | [Multi-tenant & CI/CD](Playwright-OWUI/05-multi-tenant-ci/) | 3-4h | Expert | 8 |

[README Playwright-OWUI](Playwright-OWUI/README.md)

---

**Version** : 1.1.0
**Dernière mise à jour** : 2026-03-08
**Status** : Production Ready
**License** : Projet Educatif CoursIA

---

🎓 **Bon apprentissage avec l'écosystème GenAI Images CoursIA !**

*Créé avec ❤️ par l'équipe CoursIA | Architecture SDDD | Compatible MCP*
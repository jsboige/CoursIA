> **ARCHIVED 2026-07-24** — PM transiente, valeur = historique uniquement. INDEX-only (no external inbound refs on `origin/main`). See #7422 triage.

# 🎨 Standards de Développement GenAI Images - CoursIA

**Date :** 7 octobre 2025  
**Méthode :** SDDD avec Pattern Recognition CoursIA  
**Mission :** Phase 3.1 - Standards Unifiés pour Écosystème GenAI Images

---

## 🎯 Principes Architecturaux SDDD

### 1. Héritage des Patterns CoursIA ✅

**CONFORMITÉ TOTALE** aux conventions existantes identifiées via recherche sémantique :
- **Nommage séquentiel** : `00-`, `01-`, `02-`, `03-`, `04-`
- **Structure modulaire** : Répertoires par spécialisation
- **Progression pédagogique** : 🟢→🟠→🔴 avec tags descriptifs
- **Architecture MCP** : Cellules "parameters" + mode hybride widgets/batch

### 2. Extension Contrôlée pour GenAI Images

**NOUVEAUTÉ INTÉGRÉE** dans l'existant sans régression :
- **API-First** : OpenRouter prioritaire, Docker optionnel
- **Multi-modèles** : GPT-5, Qwen-Image-Edit-2509, FLUX, Stable Diffusion
- **Templates automatisés** : Génération structure cohérente

---

## 📁 Structure Organisationnelle Standardisée

### Architecture Répertoires

```
MyIA.AI.Notebooks/GenAI/
├── 📁 00-GenAI-Environment/              # 🟢 Setup & Configuration
│   ├── 00-Environment-Validation.ipynb    # Validation APIs + Docker
│   ├── 01-OpenRouter-Configuration.ipynb  # Configuration OpenRouter
│   └── 02-Docker-Services-Setup.ipynb    # Services Docker (optionnel)
│
├── 📁 01-Images-Foundation/              # 🟢 Modèles de Base  
│   ├── 01-OpenAI-DALLE-Intro.ipynb       # DALL-E 3 via OpenAI
│   ├── 02-OpenRouter-GPT5-Vision.ipynb   # GPT-5 Vision via OpenRouter
│   └── 03-Stable-Diffusion-Basics.ipynb # SD 3.5 local/Docker
│
├── 📁 02-Images-Advanced/               # 🟠 Techniques Avancées
│   ├── 01-Qwen-Image-Edit-2509.ipynb     # Édition d'images Qwen
│   ├── 02-FLUX1-Creative-Generation.ipynb # FLUX.1 créatif
│   └── 03-ComfyUI-Workflows.ipynb        # Workflows ComfyUI
│
├── 📁 03-Images-Orchestration/          # 🔴 Multi-Modèles
│   ├── 01-Multi-Model-Pipeline.ipynb     # Pipeline orchestré
│   ├── 02-Hybrid-Cloud-Local.ipynb       # Architecture hybride
│   └── 03-Batch-Processing.ipynb         # Traitement en lot
│
├── 📁 04-Images-Applications/           # 🔴 Applications Complètes
│   ├── 01-Educational-Content.ipynb      # Contenu éducatif 
│   ├── 02-Technical-Diagrams.ipynb       # Diagrammes techniques
│   └── 03-Cross-Stitch-Patterns.ipynb   # Patterns point de croix (upgrade existant)
│
└── 📁 Templates/                        # 🎯 Templates Automatisés
    ├── base-genai-template.ipynb         # Template de base
    ├── api-notebook-template.ipynb       # Template API
    └── docker-notebook-template.ipynb    # Template Docker
```

---

## 🏷️ Conventions de Nommage

### 1. Notebooks Pédagogiques

**Pattern Principal :**
```
[Module]/[Niveau]-[Numéro]-[Technologie]-[Fonctionnalité].ipynb
```

**Exemples Conformes :**
- `01-Images-Foundation/01-OpenAI-DALLE-Intro.ipynb`
- `02-Images-Advanced/02-FLUX1-Creative-Generation.ipynb`
- `04-Images-Applications/03-Cross-Stitch-Patterns.ipynb`

### 2. Fichiers de Support

**Configurations :**
- `.env` : Variables d'environnement (sécurisées via .gitignore)
- `.env.example` : Template public avec placeholders
- `requirements.txt` : Dépendances Python par module
- `settings.json` : Configuration notebooks C#/.NET

**Ressources :**
- `images/` : Images d'exemple et assets
- `outputs/` : Générations sauvegardées
- `templates/` : Templates et patterns

---

## 📋 Standards Techniques

### 1. Structure Notebook Standardisée

**Template Obligatoire :**

```python
# =======================================
# CELLULE 1 : En-tête Markdown
# =======================================
"""
# 🎨 [TITRE DESCRIPTIF]

**Module :** [NOM_MODULE]  
**Niveau :** [🟢/🟠/🔴] [Débutant/Intermédiaire/Avancé]  
**Technologies :** [OpenRouter, GPT-5, DALL-E, etc.]  
**Durée estimée :** [XX minutes]  

## 🎯 Objectifs d'Apprentissage

- [ ] Objectif 1 spécifique et mesurable
- [ ] Objectif 2 technique concret  
- [ ] Objectif 3 application pratique

## 📚 Prérequis

- Configuration OpenRouter (.env)
- Connaissance de base des APIs
- [Autres prérequis spécifiques]
"""

# =======================================
# CELLULE 2 : Parameters Papermill (OBLIGATOIRE)
# =======================================
# Parameters cell - JAMAIS modifier ce commentaire
# Tags: ["parameters"] in notebook metadata

# Configuration pour exécution batch/MCP
notebook_mode = "interactive"  # "interactive" ou "batch" 
api_provider = "openrouter"    # "openrouter", "openai", "local"
skip_widgets = False           # True pour mode batch MCP
debug_level = "INFO"           # "DEBUG", "INFO", "WARNING", "ERROR"

# =======================================
# CELLULE 3 : Setup Environnement (STANDARDISÉ)
# =======================================
# Setup standardisé CoursIA GenAI
%load_ext autoreload
%autoreload 2

import os
import sys
from pathlib import Path
from dotenv import load_dotenv

# Configuration paths CoursIA
GENAI_ROOT = Path(__file__).parent if '__file__' in locals() else Path.cwd()
ENV_FILE = GENAI_ROOT / '.env'

# Chargement environnement
if ENV_FILE.exists():
    load_dotenv(ENV_FILE)
    print(f"✅ Configuration chargée depuis {ENV_FILE}")
else:
    print(f"⚠️  Fichier .env non trouvé : {ENV_FILE}")
    print("📖 Voir documentation configuration dans 00-GenAI-Environment/")

# =======================================
# CELLULE 4 : Imports et Validations (STANDARDISÉ)  
# =======================================
# Imports génériques GenAI
import json
import asyncio
import warnings
from typing import Dict, List, Optional, Any

# Validation APIs disponibles
def validate_genai_environment():
    """Validation environnement GenAI CoursIA"""
    status = {"openrouter": False, "openai": False, "local_docker": False}
    
    # OpenRouter (prioritaire)
    if os.getenv("OPENROUTER_API_KEY"):
        status["openrouter"] = True
        print("✅ OpenRouter API configuré")
    else:
        print("❌ OpenRouter API manquant - Voir .env.example")
    
    # OpenAI (fallback)
    if os.getenv("OPENAI_API_KEY"):
        status["openai"] = True
        print("✅ OpenAI API disponible")
    
    return status

# Validation automatique
api_status = validate_genai_environment()
```

### 2. Configuration .env Standardisée

**Variables Obligatoires :**
```bash
# === Configuration OpenRouter (Prioritaire) ===
OPENROUTER_API_KEY=sk-or-v1-your-key-here
OPENROUTER_BASE_URL="https://openrouter.ai/api/v1"
OPENROUTER_APP_NAME="CoursIA-GenAI"

# === Configuration OpenAI (Fallback) ===
OPENAI_API_KEY=sk-proj-your-key-here
OPENAI_BASE_URL="https://api.openai.com/v1"

# === Configuration Docker Local (Optionnel) ===
FLUX_API_URL="http://localhost:8001"
STABLE_DIFFUSION_URL="http://localhost:7860"
COMFYUI_API_URL="http://localhost:8188"

# === Configuration Générale ===
GENAI_DEFAULT_MODEL="gpt-4o-2024-08-06"
GENAI_TIMEOUT_SECONDS=300
GENAI_MAX_RETRIES=3
GENAI_OUTPUT_DIR="outputs"
```

### 3. Gestion d'Erreurs Standardisée

**Pattern Error Handling :**
```python
class GenAIError(Exception):
    """Erreur base écosystème GenAI CoursIA"""
    pass

class APIConnectionError(GenAIError):
    """Erreur connexion API (OpenRouter, OpenAI, etc.)"""
    pass

class ModelNotAvailableError(GenAIError):
    """Modèle demandé indisponible"""
    pass

def safe_api_call(func, *args, **kwargs):
    """Appel API sécurisé avec gestion d'erreurs standardisée"""
    max_retries = int(os.getenv("GENAI_MAX_RETRIES", 3))
    
    for attempt in range(max_retries):
        try:
            return func(*args, **kwargs)
        except Exception as e:
            if attempt == max_retries - 1:
                raise APIConnectionError(f"Échec après {max_retries} tentatives: {e}")
            print(f"⚠️  Tentative {attempt + 1} échouée, retry...")
            time.sleep(2 ** attempt)  # Exponential backoff
```

---

## 🎓 Standards Pédagogiques

### 1. Progression de Complexité

**🟢 Niveau Débutant (00-01) :**
- **Concepts :** Configuration, premiers appels API, génération simple
- **Durée :** 15-30 minutes par notebook
- **Prérequis :** Connaissance Python de base
- **Outputs :** 1-3 images générées avec prompts simples

**🟠 Niveau Intermédiaire (02) :**
- **Concepts :** Paramètres avancés, édition, workflows
- **Durée :** 30-60 minutes par notebook  
- **Prérequis :** Notebooks Foundation complétés
- **Outputs :** Comparaisons multi-modèles, éditions complexes

**🔴 Niveau Avancé (03-04) :**
- **Concepts :** Orchestration, pipelines, applications complètes
- **Durée :** 60+ minutes par notebook
- **Prérequis :** Maîtrise niveaux précédents
- **Outputs :** Applications utilisables, code réutilisable

### 2. Tags et Métadonnées

**Tags Obligatoires par Notebook :**
```json
{
  "metadata": {
    "genai_tags": ["openrouter", "gpt-5", "image-generation"],
    "difficulty": "beginner|intermediate|advanced", 
    "estimated_duration_minutes": 30,
    "prerequisites": ["00-Environment-Validation"],
    "learning_outcomes": [
      "Configurer OpenRouter pour génération d'images",
      "Utiliser GPT-5 Vision pour analyse d'images"
    ]
  }
}
```

### 3. Documentation Inline

**Commentaires Standardisés :**
```python
# 🎯 OBJECTIF : [Description claire de la section]
# 📝 EXPLICATION : [Concepts théoriques importants]  
# ⚡ ACTION : [Ce que fait le code concrètement]
# 💡 ASTUCE : [Conseils d'optimisation ou bonnes pratiques]
# ⚠️  ATTENTION : [Points d'attention ou erreurs courantes]
# 🔧 PARAMÈTRES : [Explication des paramètres modifiables]
# 📊 RÉSULTATS ATTENDUS : [Ce qu'on devrait voir]
```

---

## 🔧 Standards d'Intégration MCP

### 1. Compatibilité Mode Batch

**Cellule Parameters Obligatoire :**
- Tags: `["parameters"]` dans les métadonnées
- Variables configurables pour MCP
- Mode `skip_widgets=True` pour exécution automatisée

**Pattern Widgets Hybrides :**
```python
# Mode hybride : widgets interactifs OU configuration batch
if skip_widgets:
    # Configuration automatique pour MCP
    selected_model = api_provider
    generation_count = 3
    prompt_complexity = "moderate"
else:
    # Widgets interactifs pour usage manuel
    from ipywidgets import interact, widgets
    # [Code widgets interactifs]
```

### 2. Monitoring et Logging

**Logging Standardisé :**
```python
import logging

# Configuration logging CoursIA GenAI
logger = logging.getLogger('coursia_genai')
logger.setLevel(getattr(logging, debug_level))

# Handler pour notebook (si pas déjà configuré)
if not logger.handlers:
    handler = logging.StreamHandler()
    formatter = logging.Formatter(
        '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )
    handler.setFormatter(formatter)
    logger.addHandler(handler)

# Usage dans le notebook
logger.info("🚀 Démarrage génération d'images")
logger.debug(f"Configuration: {api_provider}, modèle: {selected_model}")
```

---

## 📊 Standards de Validation

### 1. Tests Automatisés

**Validation Notebook :**
```python
def validate_notebook_setup():
    """Tests automatisés pour validation notebook"""
    tests_passed = 0
    total_tests = 0
    
    # Test 1: Configuration environnement
    total_tests += 1
    if api_status.get("openrouter") or api_status.get("openai"):
        print("✅ API disponible")
        tests_passed += 1
    else:
        print("❌ Aucune API configurée")
    
    # Test 2: Répertoires de sortie
    total_tests += 1
    output_dir = Path(os.getenv("GENAI_OUTPUT_DIR", "outputs"))
    if output_dir.exists() or output_dir.mkdir(parents=True, exist_ok=True):
        print(f"✅ Répertoire de sortie: {output_dir}")
        tests_passed += 1
    else:
        print(f"❌ Impossible de créer {output_dir}")
    
    # Résultat final
    success_rate = (tests_passed / total_tests) * 100
    print(f"\n📊 Validation: {tests_passed}/{total_tests} ({success_rate:.1f}%)")
    return success_rate > 80

# Validation automatique dans chaque notebook
assert validate_notebook_setup(), "❌ Échec validation environnement"
```

### 2. Benchmarks Performance

**Métriques Standardisées :**
- **Temps de génération** par image/modèle
- **Qualité perçue** (échelle 1-5 utilisateur)
- **Coût par génération** (tokens/API calls)
- **Taux de succès** génération

---

## 🚀 Scripts d'Automatisation

### 1. Génération Template Notebook

**Script :** `scripts/generate-genai-notebook.ps1`
```powershell
param(
    [string]$NotebookName,
    [string]$Module,
    [string]$Level = "beginner",
    [string]$Technology
)

# Génération automatique structure notebook selon standards
```

### 2. Validation Standards

**Script :** `scripts/validate-genai-standards.py`
```python
def validate_notebook_standards(notebook_path):
    """Validation conformité standards CoursIA GenAI"""
    # Vérification structure cellules
    # Validation métadonnées
    # Contrôle conventions nommage
    # Test exécution basique
```

---

## 📚 Documentation et Maintenance

### 1. README par Module

**Template README.md :**
```markdown
# 📁 [NOM_MODULE] - GenAI Images CoursIA

## 🎯 Vue d'Ensemble
[Description du module et objectifs]

## 📋 Liste des Notebooks
[Tableau avec nom, difficulté, durée, prérequis]

## 🛠️ Configuration Requise
[Prérequis techniques spécifiques]

## 🚀 Démarrage Rapide
[Instructions minimales pour commencer]
```

### 2. Mise à Jour Standards

**Processus :**
1. **Proposition** via issue GitHub avec label `genai-standards`
2. **Discussion** communauté et validation technique
3. **Implémentation** avec backward compatibility
4. **Documentation** mise à jour automatique
5. **Migration** notebooks existants (scripts automatisés)

---

## ✅ Checklist Conformité

### Avant Publication Notebook

- [ ] **Structure :** Cellules dans l'ordre standardisé
- [ ] **Parameters :** Cellule parameters avec tags corrects
- [ ] **Documentation :** En-tête complet avec objectifs
- [ ] **Validation :** Tests automatisés passent
- [ ] **Configuration :** Variables .env documentées
- [ ] **Logging :** Messages d'état appropriés
- [ ] **Outputs :** Exemples de résultats inclus
- [ ] **README :** Documentation module mise à jour

### Avant Commit Git

- [ ] **Sécurité :** Aucune clé API en dur
- [ ] **Gitignore :** Fichiers sensibles exclus
- [ ] **Tests :** Exécution complète sans erreur
- [ ] **Nommage :** Conventions respectées
- [ ] **Métadonnées :** Tags et durée renseignés

---

*Standards conçus avec SDDD - Évolution continue basée sur usage réel*
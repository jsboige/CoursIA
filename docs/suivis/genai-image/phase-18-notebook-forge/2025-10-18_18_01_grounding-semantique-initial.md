# Grounding Sémantique Initial - Phase 18 Notebook Forge

**Date**: 2025-10-18 18:01:00  
**Phase**: 18 - Développement Notebook Forge API SD XL Turbo  
**Objectif**: Recherche sémantique pour informer le design du notebook pédagogique

---

## Recherches Effectuées

### 1. Notebooks GenAI Existants

**Requête**: `"notebooks GenAI Python API REST Stable Diffusion génération images pédagogique"`

#### Patterns Pédagogiques Identifiés

**Structure Modulaire Cohérente**:
```
MyIA.AI.Notebooks/GenAI/
├── 00-GenAI-Environment/        # Setup & configuration (4 notebooks)
├── 01-Images-Foundation/         # Introduction GenAI images (4 notebooks)
├── 02-Images-Advanced/           # Techniques avancées (3 notebooks)
├── 03-Expert-Workflows/          # Workflows experts (7 notebooks)
└── 04-Images-Applications/       # Applications pratiques (3 notebooks)
```

**Progression Pédagogique**:
- 🟢 **Foundation** (2-3h) - Débutant - Module 00 + 01
- 🟠 **Advanced** (4-5h) - Intermédiaire - Module 02
- 🔴 **Expert** (6-8h) - Avancé - Module 03 + 04
- **Total**: ~15h de formation complète

**Patterns Code Réutilisables**:

1. **Helper Functions Pattern** ([`docs/genai/phase2-templates.md:418-453`](docs/genai/phase2-templates.md)):
```python
def generate_image_cloud(prompt, cloud_model, **kwargs):
    """Génération via API cloud (OpenRouter)"""
    headers = {
        'Authorization': f'Bearer {self.config.openrouter_key}',
        'Content-Type': 'application/json'
    }
    payload = {'model': cloud_model, 'prompt': prompt, **kwargs}
    response = self.session.post(
        'https://openrouter.ai/api/v1/generate',
        headers=headers, json=payload
    )
    return response.json()
```

2. **Class-Based API Wrapper** ([`MyIA.AI.Notebooks/GenAI/tutorials/dalle3-complete-guide.md`](MyIA.AI.Notebooks/GenAI/tutorials/dalle3-complete-guide.md)):
```python
class EducationalImageGenerator:
    """Wrapper pédagogique pour APIs génération images"""
    def __init__(self, api_url, auth=None):
        self.api_url = api_url
        self.auth = auth
    
    def generate(self, prompt, **params):
        # Génération + logging pédagogique
        pass
```

3. **Structure Cellules Standard** ([`docs/genai/development-standards.md:98-102`](docs/genai/development-standards.md)):
```markdown
# Cellule 1: Markdown - Introduction
# Cellule 2: Code - Imports + Configuration
# Cellule 3: Markdown - Explication concept
# Cellule 4: Code - Exemple pratique
# Cellule 5: Markdown - Conseils
# Cellule N: Code - Exercice pratique
```

**Fichiers Support Disponibles**:
- [`shared/helpers/comfyui_client.py`](MyIA.AI.Notebooks/GenAI/shared/helpers/comfyui_client.py) - Client ComfyUI
- [`shared/helpers/genai_helpers.py`](MyIA.AI.Notebooks/GenAI/shared/helpers/genai_helpers.py) - Helpers génération

---

### 2. API Forge Documentation

**Requête**: `"Stable Diffusion Forge API REST endpoints txt2img parameters exemples Python"`

#### API SD XL Turbo Validée

**Source**: [`docs/suivis/genai-image/GUIDE-APIS-ETUDIANTS.md:148-188`](docs/suivis/genai-image/GUIDE-APIS-ETUDIANTS.md)

**Configuration Production**:
- **URL**: https://turbo.stable-diffusion-webui-forge.myia.io
- **Authentication**: Basic Auth (credentials enseignant)
- **GPU**: RTX 3090 (24GB VRAM) - GPU 1 dédié
- **Modèle**: turbovisionxlSuperFastXLBasedOnNew v4.31 (~6.5GB)
- **Status**: ✅ OPÉRATIONNEL (validé Phase 16)

**Endpoints Critiques**:

1. **Health Check**: `GET /` - Page accueil Gradio
2. **Liste Modèles**: `GET /sdapi/v1/sd-models`
3. **Liste Samplers**: `GET /sdapi/v1/samplers`
4. **Génération**: `POST /sdapi/v1/txt2img` ⭐ (endpoint principal)

**Format Requête txt2img** ([`docs/suivis/genai-image/phase-14b-tests-apis/2025-10-16_14B_01_grounding-semantique-initial.md:59-106`](docs/suivis/genai-image/phase-14b-tests-apis/2025-10-16_14B_01_grounding-semantique-initial.md)):
```json
{
  "prompt": "description détaillée",
  "negative_prompt": "ce qu'il faut éviter",
  "steps": 4,           // Turbo optimisé: 4-8 steps
  "width": 512,
  "height": 512,
  "cfg_scale": 2.0,    // Turbo recommandé: 1.5-3.0
  "sampler_name": "Euler",
  "scheduler": "simple"
}
```

**Exemple Python Fonctionnel** (guide étudiants):
```python
import requests
import base64
from io import BytesIO
from PIL import Image

BASE_URL = "https://turbo.stable-diffusion-webui-forge.myia.io"
AUTH = ("username", "password")  # Fournis par enseignant

def generate_image_turbo(prompt, negative_prompt="", steps=4):
    """
    Génération rapide avec SD XL Turbo
    Note: Steps réduits (4-8) car modèle "turbo" optimisé
    """
    payload = {
        "prompt": prompt,
        "negative_prompt": negative_prompt,
        "steps": steps,
        "width": 1024,
        "height": 1024,
        "cfg_scale": 2.0,
        "sampler_name": "Euler",
        "scheduler": "simple"
    }
    
    response = requests.post(
        f"{BASE_URL}/sdapi/v1/txt2img",
        json=payload,
        auth=AUTH,
        timeout=30
    )
    
    if response.status_code == 200:
        result = response.json()
        # Décodage image base64
        image_data = base64.b64decode(result['images'][0])
        return Image.open(BytesIO(image_data))
```

**Paramètres Optimaux SD XL Turbo**:
- ⚡ **Steps**: 4-8 (vs 20-50 standard)
- 🎚️ **CFG Scale**: 1.5-3.0 (vs 7.5 standard)
- 🖼️ **Résolutions**: 512x512, 768x768, 1024x1024
- ⏱️ **Latence**: 1-3s par génération
- 💾 **VRAM**: 4-6GB par génération

**Performance Mesurée** (Phase 16):
- **Durée totale tests**: 18.78 secondes (4 endpoints)
- **Temps moyen/endpoint**: ~4.70s
- **Stabilité**: 100% succès
- **Conclusion**: ✅ OPÉRATIONNEL pour prototypage étudiants

---

### 3. Pattern LocalLlama à Migrer

**Requête**: `"notebook 4_LocalLlama API locale Python structure pédagogique cellules"`

#### Absence du Fichier Source

**Constat**: Le fichier [`MyIA.AI.Notebooks/GenAI/4_LocalLlama.ipynb`](MyIA.AI.Notebooks/GenAI/4_LocalLlama.ipynb) n'apparaît **pas** dans les résultats de recherche sémantique.

**Hypothèses**:
1. Fichier peut-être non indexé dans la base vectorielle
2. Fichier peut-être renommé ou déplacé
3. Fichier peut-être dans un répertoire parent différent

**Action Requise**: Vérifier existence fichier avant de continuer avec MCP `jupyter-papermill`.

#### Patterns Généraux Notebooks API Locale

**Structure Standard Identifiée** ([`docs/genai/development-standards.md:98-102`](docs/genai/development-standards.md)):

```python
# CELLULE 1: Markdown - Introduction
"""
# Notebook: [Titre]
**Objectif**: [Description]
**Prérequis**: [Technologies]
"""

# CELLULE 2: Code - Parameters (Papermill)
# Parameters for Papermill execution
skip_widgets = True
api_url = "http://localhost:8000"
debug_mode = False

# CELLULE 3: Code - Imports + Configuration
import requests
import json
from typing import Dict, Optional
import matplotlib.pyplot as plt

# Configuration
API_URL = api_url
TIMEOUT = 30

# CELLULE 4: Markdown - Explication API
"""
## Architecture API
[Explications techniques]
"""

# CELLULE 5: Code - Helper Functions
def call_api(endpoint: str, payload: Dict) -> Dict:
    """Helper pour appels API"""
    response = requests.post(
        f"{API_URL}/{endpoint}",
        json=payload,
        timeout=TIMEOUT
    )
    return response.json()

# CELLULE 6: Markdown - Exemple Simple
"""
### Exemple 1: Requête Basique
"""

# CELLULE 7: Code - Exemple Simple
result = call_api("generate", {"prompt": "Hello world"})
print(result)

# CELLULE 8+: Exemples avancés...
```

**Éléments Clés à Adapter**:
1. ✅ **Cellule Parameters** - Pour exécution Papermill
2. ✅ **Helper Functions** - Encapsulation appels API
3. ✅ **Gestion Erreurs** - Try/except avec messages pédagogiques
4. ✅ **Visualisation** - Affichage résultats (matplotlib, PIL)
5. ✅ **Progression** - Du simple au complexe

---

## Design Notebook Cible - Structure Prévisionnelle

### Objectifs Pédagogiques

1. Comprendre API REST Stable Diffusion Forge
2. Maîtriser génération texte→image rapide (prototypage)
3. Explorer paramètres SD XL Turbo optimaux
4. Comparer avec API Qwen (workflow hybride)

### Structure Notebook (12 cellules)

#### Cellule 1: Markdown - Introduction
```markdown
# Notebook: Stable Diffusion Forge SD XL Turbo

**Module**: 00-GenAI-Environment (ou 01-Images-Foundation?)
**Niveau**: 🟢 Débutant
**Durée**: 30-45 minutes

## Objectifs
- Comprendre API REST Forge (Automatic1111 compatible)
- Générer images rapidement (1-3s) pour prototypage
- Comparer Turbo vs Qwen (workflow recommandé)

## Prérequis
- Python 3.10+
- Packages: requests, Pillow, matplotlib
- Credentials API (fournis par enseignant)
```

#### Cellule 2: Code - Parameters (Papermill)
```python
# Parameters for Papermill execution
skip_auth_prompt = False  # Si True, utilise .env
api_url = "https://turbo.stable-diffusion-webui-forge.myia.io"
example_prompt = "A serene mountain landscape at sunset"
```

#### Cellule 3: Code - Imports + Configuration
```python
import requests
import base64
import json
from io import BytesIO
from PIL import Image
import matplotlib.pyplot as plt
from typing import Optional, Dict, Any

# Configuration API
BASE_URL = api_url
TIMEOUT = 30
```

#### Cellule 4: Markdown - Architecture API Forge
```markdown
## API Stable Diffusion Forge

### Qu'est-ce que Forge?
- Fork optimisé de Automatic1111 WebUI
- Compatible API standard Stable Diffusion
- Accélération GPU optimale (RTX 3090)

### Endpoints Principaux
1. `/sdapi/v1/txt2img` - Génération text-to-image
2. `/sdapi/v1/sd-models` - Liste modèles
3. `/sdapi/v1/samplers` - Liste samplers
```

#### Cellule 5: Code - Authentification (Interactive ou .env)
```python
# Gestion authentification
if skip_auth_prompt:
    from dotenv import load_dotenv
    import os
    load_dotenv()
    AUTH = (os.getenv("FORGE_USERNAME"), os.getenv("FORGE_PASSWORD"))
    print("✅ Authentification chargée depuis .env")
else:
    import getpass
    username = input("Username Forge API: ")
    password = getpass.getpass("Password: ")
    AUTH = (username, password)
    print("✅ Authentification saisie")
```

#### Cellule 6: Code - Helper Function Principale
```python
def generate_image_turbo(
    prompt: str,
    negative_prompt: str = "",
    steps: int = 4,
    width: int = 512,
    height: int = 512,
    cfg_scale: float = 2.0,
    sampler_name: str = "Euler"
) -> Optional[Image.Image]:
    """
    Génère une image via API Forge SD XL Turbo
    
    Args:
        prompt: Description de l'image désirée
        negative_prompt: Éléments à éviter
        steps: Nombre d'itérations (4-8 recommandé pour Turbo)
        width, height: Dimensions (512, 768, 1024)
        cfg_scale: Guidance scale (1.5-3.0 pour Turbo)
        sampler_name: Algorithme sampling
    
    Returns:
        Image PIL ou None si erreur
    """
    payload = {
        "prompt": prompt,
        "negative_prompt": negative_prompt,
        "steps": steps,
        "width": width,
        "height": height,
        "cfg_scale": cfg_scale,
        "sampler_name": sampler_name,
        "scheduler": "simple"
    }
    
    try:
        response = requests.post(
            f"{BASE_URL}/sdapi/v1/txt2img",
            json=payload,
            auth=AUTH,
            timeout=TIMEOUT
        )
        response.raise_for_status()
        
        result = response.json()
        image_data = base64.b64decode(result['images'][0])
        image = Image.open(BytesIO(image_data))
        
        print(f"✅ Image générée: {width}x{height}, {steps} steps")
        return image
        
    except requests.exceptions.RequestException as e:
        print(f"❌ Erreur API: {e}")
        return None
```

#### Cellule 7: Markdown - Paramètres Optimaux Turbo
```markdown
## Optimisation SD XL Turbo

### Différences Clés vs Standard
| Paramètre | Standard | Turbo | Raison |
|-----------|----------|-------|--------|
| Steps | 20-50 | 4-8 | Distillation modèle |
| CFG Scale | 7.5 | 1.5-3.0 | Guidance réduite |
| Latence | 10-30s | 1-3s | Optimisation inférence |

### Recommandations
- ⚡ **Prototypage**: steps=4, cfg=2.0
- 🎨 **Qualité**: steps=6-8, cfg=2.5
- 🖼️ **Résolutions**: 512x512 (rapide), 1024x1024 (détaillé)
```

#### Cellule 8: Code - Exemple Simple
```python
# Génération simple avec paramètres par défaut
image = generate_image_turbo(
    prompt=example_prompt,
    negative_prompt="blurry, low quality",
    steps=4,
    width=512,
    height=512
)

if image:
    plt.figure(figsize=(8, 8))
    plt.imshow(image)
    plt.axis('off')
    plt.title(f"Prompt: {example_prompt}")
    plt.show()
```

#### Cellule 9: Markdown - Cas d'Usage Avancés
```markdown
## Workflows Recommandés

### 1. Exploration Rapide (Design Thinking)
1. Générer 5-10 variations (steps=4)
2. Sélectionner meilleure direction
3. Affiner avec Qwen (steps=30)

### 2. Comparaison Prompts
- Tester multiples formulations
- Grid display résultats
- Analyse différences visuelles
```

#### Cellule 10: Code - Exemple Comparaison Prompts
```python
# Comparaison variations prompt
prompts = [
    "A futuristic city at night",
    "A futuristic city at night, neon lights",
    "A futuristic city at night, cyberpunk style, rain"
]

images = []
for p in prompts:
    img = generate_image_turbo(p, steps=6, width=512, height=512)
    if img:
        images.append((p, img))

# Affichage grid
fig, axes = plt.subplots(1, len(images), figsize=(15, 5))
for idx, (prompt, img) in enumerate(images):
    axes[idx].imshow(img)
    axes[idx].axis('off')
    axes[idx].set_title(prompt[:30] + "...", fontsize=10)
plt.tight_layout()
plt.show()
```

#### Cellule 11: Markdown - Bonnes Pratiques
```markdown
## Bonnes Pratiques API Forge

### 1. Gestion Erreurs
- Toujours `try/except` sur appels API
- Logger erreurs pour débogage
- Fallback graceful si échec

### 2. Performance
- Limiter résolution pour tests (512x512)
- Utiliser steps=4 pour exploration
- Batch generation non supporté (1 image/appel)

### 3. Workflow Hybride (Recommandé)
1. 🚀 **Phase Exploration**: Forge Turbo (rapide)
2. 🎨 **Phase Raffinement**: Qwen (qualité)
3. 📝 **Phase Production**: Qwen + custom nodes
```

#### Cellule 12: Code - Exercice Pratique
```python
# 🎯 EXERCICE: Créez votre propre génération

# TODO: Modifiez les paramètres ci-dessous
YOUR_PROMPT = "A beautiful landscape..."  # Votre description
YOUR_NEGATIVE = "blurry, low quality"      # Éléments à éviter
YOUR_STEPS = 6                             # 4-8 recommandé
YOUR_WIDTH = 768                           # 512, 768, ou 1024
YOUR_HEIGHT = 768

# Génération
your_image = generate_image_turbo(
    prompt=YOUR_PROMPT,
    negative_prompt=YOUR_NEGATIVE,
    steps=YOUR_STEPS,
    width=YOUR_WIDTH,
    height=YOUR_HEIGHT
)

# Affichage
if your_image:
    plt.figure(figsize=(10, 10))
    plt.imshow(your_image)
    plt.axis('off')
    plt.title(f"Votre création: {YOUR_PROMPT[:50]}...")
    plt.show()
    print("✅ Exercice complété!")
else:
    print("❌ Échec génération - vérifiez vos paramètres")
```

---

## Validation Pédagogique Préliminaire

### Critères Validés ✅

- ✅ **Progression logique**: Intro → Config → Helpers → Exemples → Exercice
- ✅ **Exemples concrets**: Code fonctionnel reproductible
- ✅ **Exercice pratique**: Template à compléter par étudiant
- ✅ **Gestion erreurs**: Try/except avec messages pédagogiques
- ✅ **Documentation inline**: Commentaires explicatifs abondants
- ✅ **Comparaison Qwen**: Positionnement workflow hybride
- ✅ **Durée raisonnable**: 30-45 min (12 cellules)

### Points d'Attention ⚠️

1. **Fichier source 4_LocalLlama.ipynb**: Vérifier existence avant analyse détaillée
2. **Placement module**: 00-GenAI-Environment (setup) ou 01-Images-Foundation (intro)?
3. **Credentials**: Système `.env` ou input interactif?

---

## Mise à Jour TODO Phase 18

### Ajustements Identifiés

**Ajout tâche préliminaire**:
```markdown
[ ] 2.5. Vérification existence 4_LocalLlama.ipynb (avant lecture MCP)
```

**Raison**: Fichier non trouvé par recherche sémantique, nécessite vérification système fichiers.

**Actions correctives possibles**:
1. Rechercher fichier via `list_files` ou `search_files`
2. Si absent: Adapter design sans migration directe
3. Si présent: Procéder lecture MCP comme prévu

---

## Conclusions Grounding Sémantique Initial

### Patterns Réutilisables Identifiés

1. ✅ **Structure modulaire notebooks GenAI** - 00-04 modules cohérents
2. ✅ **Helper functions pattern** - Encapsulation API calls
3. ✅ **Progression pédagogique** - Simple → Complexe → Exercice
4. ✅ **Documentation API Forge** - Guide étudiants complet validé
5. ✅ **Paramètres optimaux Turbo** - Steps=4-8, CFG=1.5-3.0

### Design Notebook Cible Validé

- **12 cellules** structurées logiquement
- **Markdown + Code** alternés pédagogiquement
- **Helper function** `generate_image_turbo()` centrale
- **Exemples progressifs** + **Exercice pratique**
- **Workflow hybride** Turbo→Qwen expliqué

### Prochaines Étapes

1. ✅ Vérifier existence `4_LocalLlama.ipynb`
2. ⏭️ Grounding Conversationnel (MCP `roo-state-manager`)
3. ⏭️ Analyse source détaillée (MCP `jupyter-papermill`)
4. ⏭️ Design final notebook
5. ⏭️ Checkpoint SDDD validation

---

**Document créé par**: Roo Code Complex Mode  
**Méthodologie**: SDDD Phase 18 - Grounding Sémantique Initial  
**Prochaine étape**: Vérification fichier source + Grounding Conversationnel
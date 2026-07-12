# Guide APIs Génération Images - Étudiants CoursIA

**Version**: 1.0  
**Date**: 2025-10-16  
**Public**: Étudiants Master IA  
**Prérequis**: Python 3.10+, bases REST API

---

## 🎯 Vue d'Ensemble

CoursIA met à votre disposition **2 APIs complémentaires** de génération d'images par IA:

| API | Cas d'usage | Force | Latence |
|-----|-------------|-------|---------|
| **Qwen Image-Edit 2.5** | Production, édition avancée | Multimodal haute qualité | 5-10s |
| **SD XL Turbo** | Prototypage rapide | Vitesse, itérations | 1-3s |
| **Z-Image Turbo (Lumina)** | Génération ultra-rapide next-gen | Qualité photoréaliste + Vitesse | 2-4s |

**Recommandation workflow**:
1. 🚀 **Exploration** → SD XL Turbo (itérations rapides)
2. 🎨 **Raffinement** → Qwen (qualité production)
3. 📝 **Production finale** → Qwen (contrôle précis)

---

## 📚 Table des Matières

1. [API 1: Qwen Image-Edit 2.5](#api-1-qwen-image-edit-25)
2. [API 2: SD XL Turbo (Forge)](#api-2-sd-xl-turbo-forge)
3. [API 3: Z-Image Turbo (Lumina-Next)](#api-3-z-image-turbo-lumina-next)
4. [Comparaison Technique](#comparaison-technique)
5. [Exemples Pratiques](#exemples-pratiques)
6. [Troubleshooting](#troubleshooting)
7. [Ressources Complémentaires](#ressources-complémentaires)

---

## API 1: Qwen Image-Edit 2.5

### 🎯 Présentation

**Qwen Image-Edit** est un modèle multimodal avancé capable de:
- ✅ Génération text-to-image haute qualité
- ✅ Édition d'images guidée par texte
- ✅ Compréhension contextuelle avancée
- ✅ Support multi-langues (dont français)

**Architecture**: ComfyUI + vLLM + Qwen-Image-Edit-2509-FP8  
**GPU**: RTX 3090 (24GB VRAM)  
**Modèle**: 54GB (quantification FP8)

### 🔗 Accès

- **URL Production**: `https://qwen-image-edit.myia.io`
- **API Endpoint**: Port 8188 (WebSocket)
- **Documentation complète**: [`docs/suivis/genai-image/phase-12-production/`](../suivis/genai-image/phase-12a-production/)

### 🔐 Authentification (NOUVEAU - Phase 23C)

**Depuis le 2025-10-21**, l'API Qwen requiert une authentification par token Bearer pour garantir la sécurité et la disponibilité du service.

#### Obtention du Token

**Méthode 1 - Interface Web** :
1. Accédez à https://qwen-image-edit.myia.io/login
2. Connectez-vous avec :
   - **Username** : `etudiant`
   - **Password** : `CourIA2025!`
3. Copiez le token affiché après connexion

**Methode 2 - Fourni par l'Enseignant** :
Contactez votre enseignant pour obtenir votre token personnel.

> **Note Technique** : ComfyUI-Login utilise une implementation particuliere ou le hash bcrypt EST le bearer token (pas le mot de passe en clair). Les tokens fournis sont donc des hashes commencant par `$2b$12$...`

#### Configuration dans les Notebooks

**Étape 1 : Créer le fichier `.env`**

```bash
cd MyIA.AI.Notebooks/GenAI/01-Images-Foundation/
cp .env.example .env
```

**Étape 2 : Éditer `.env` avec votre token**

```env
# Fichier: MyIA.AI.Notebooks/GenAI/01-Images-Foundation/.env
QWEN_API_TOKEN=votre_token_copie_ici
```

**Étape 3 : Le notebook charge automatiquement le token**

```python
from dotenv import load_dotenv
import os

load_dotenv()
QWEN_API_TOKEN = os.getenv("QWEN_API_TOKEN")

# Headers d'authentification (ajouté automatiquement par ComfyUIClient)
AUTH_HEADERS = {"Authorization": f"Bearer {QWEN_API_TOKEN}"}
```

#### Sécurité du Token

⚠️ **Règles CRITIQUES** :
- ❌ Ne JAMAIS partager votre token
- ❌ Ne JAMAIS commiter le fichier `.env` dans Git (déjà dans `.gitignore`)
- ✅ Utiliser TOUJOURS le fichier `.env` pour stocker le token
- ✅ Contacter l'enseignant en cas de perte du token

**Note** : Le fichier `.env` est automatiquement ignoré par Git pour votre sécurité.


### 💻 Exemple Python - Génération Simple

```python
import sys
sys.path.insert(0, '../shared')
from helpers.comfyui_client import create_client

# 1. Connexion au service
client = create_client("https://qwen-image-edit.myia.io")

# 2. Génération text-to-image
prompt_id = client.generate_text2image(
    prompt="A serene mountain landscape at sunset with a lake reflection",
    negative_prompt="blurry, low quality, distorted",
    width=1024,
    height=1024,
    steps=25,  # Plus de steps = meilleure qualité
    cfg_scale=7.5,  # Guidance (7-8 recommandé)
    seed=-1  # -1 pour aléatoire
)

print(f"Génération lancée: {prompt_id}")

# 3. Attendre et récupérer résultat
images = client.wait_for_images(prompt_id)
print(f"✅ {len(images)} image(s) générée(s)")
```

### 💻 Exemple Python - Édition Image

```python
# Éditer une image existante
from PIL import Image

# Charger image source
input_image = Image.open("mon_image.png")

# Édition guidée par texte
prompt_id = client.edit_image(
    image=input_image,
    prompt="Add a rainbow in the sky",
    strength=0.7,  # 0.0-1.0 (force modification)
    steps=30
)

edited_images = client.wait_for_images(prompt_id)
edited_images[0].save("image_editee.png")
```

### 📊 Paramètres Clefs

| Paramètre | Plage | Recommandé | Impact |
|-----------|-------|------------|--------|
| `steps` | 1-50 | 20-30 | Qualité (+ = meilleur mais + lent) |
| `cfg_scale` | 1-20 | 7-8 | Respect prompt (trop haut = artefacts) |
| `strength` | 0.0-1.0 | 0.6-0.8 | Force édition (édition seule) |
| `seed` | -1 ou int | -1 | Reproductibilité (-1 = aléatoire) |

### ⚠️ Limites & Conseils

**Limites**:
- ⏱️ Latence: 5-10s par génération
- 🖼️ Résolution max: 2048x2048 (au-delà = VRAM overflow)
- 🔄 Pas de batch generation (1 image à la fois)

**Conseils qualité**:
- 📝 Prompts détaillés en anglais donnent meilleurs résultats
- 🎨 Utiliser negative prompts pour éviter artefacts
- 🔢 Fixer seed pour reproductibilité expériences

**Notebook complet**: [`MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-5-ComfyUI-Local-Test.ipynb`](../../MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-5-ComfyUI-Local-Test.ipynb)

---

## API 2: SD XL Turbo (Forge)

### 🎯 Présentation

**SD XL Turbo** est une version optimisée de Stable Diffusion XL pour:
- ⚡ Génération ultra-rapide (1-3 secondes)
- 🎯 Prototypage et itérations rapides
- 💾 Faible consommation VRAM (4-6GB)
- 🎨 Qualité standard satisfaisante

**Architecture**: Stable Diffusion WebUI Forge  
**GPU**: RTX 3090 (24GB VRAM) - GPU 1 dédié  
**Modèle**: turbovisionxlSuperFastXLBasedOnNew v4.31 (~6.5GB)

### 🔗 Accès

- **URL Production**: `https://turbo.stable-diffusion-webui-forge.myia.io`
- **WebUI**: Interface Gradio (browser)
- **API REST**: Endpoints Forge standard
- **Authentication**: Basic Auth (credentials fournis par enseignant)

### 💻 Exemple Python - Génération Rapide (WebUI)

```python
import requests
import base64
from io import BytesIO
from PIL import Image

# Configuration
BASE_URL = "https://turbo.stable-diffusion-webui-forge.myia.io"
# Credentials fournis par l'enseignant
AUTH = ("username", "password")

def generate_image_turbo(prompt, negative_prompt="", steps=4):
    """
    Génération rapide avec SD XL Turbo
    Note: Steps réduits (4-8) car modèle "turbo" optimisé
    """
    payload = {
        "prompt": prompt,
        "negative_prompt": negative_prompt,
        "steps": steps,  # Turbo: 4-8 steps suffisent
        "width": 1024,
        "height": 1024,
        "cfg_scale": 2.0,  # Turbo: CFG bas (1.5-3.0)
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
        # Décoder image base64
        image_data = base64.b64decode(result['images'][0])
        image = Image.open(BytesIO(image_data))
        return image
    else:
        raise Exception(f"Erreur API: {response.status_code}")

# Utilisation
image = generate_image_turbo(
    prompt="A futuristic city at night, neon lights, cyberpunk style",
    negative_prompt="blurry, low quality",
    steps=6
)
image.save("turbo_output.png")
print("✅ Image générée en ~2-3 secondes")
```

### 💻 Exemple Python - Variation Rapide

```python
def generate_variations(base_prompt, variations, steps=4):
    """
    Générer rapidement plusieurs variations d'un concept
    Idéal pour exploration créative
    """
    results = []
    
    for i, variation in enumerate(variations):
        full_prompt = f"{base_prompt}, {variation}"
        print(f"Génération {i+1}/{len(variations)}: {variation}")
        
        image = generate_image_turbo(
            prompt=full_prompt,
            steps=steps
        )
        results.append((variation, image))
    
    return results

# Exploration rapide de styles
base = "A cozy coffee shop interior"
styles = [
    "modern minimalist design",
    "vintage rustic atmosphere", 
    "futuristic sci-fi aesthetic",
    "warm traditional style"
]

variations = generate_variations(base, styles, steps=4)

# Sauvegarder toutes les variations
for style, img in variations:
    filename = f"coffee_shop_{style.replace(' ', '_')}.png"
    img.save(filename)

print(f"✅ {len(variations)} variations générées en ~10 secondes")
```

### 📊 Paramètres Turbo Spécifiques

| Paramètre | Turbo | Standard | Explication |
|-----------|-------|----------|-------------|
| `steps` | **4-8** | 20-50 | Turbo optimisé pour peu de steps |
| `cfg_scale` | **1.5-3.0** | 7-8 | CFG bas car guidance intégrée |
| `sampler` | **Euler** | DPM++/DDIM | Euler plus rapide avec Turbo |

### ⚠️ Limites & Conseils

**Limites**:
- 🎨 Qualité légèrement inférieure à Qwen
- 📝 Moins bon avec prompts complexes
- 🔄 Pas d'édition image (txt2img seulement)

**Quand utiliser**:
- ✅ Phase exploration (tester 10+ concepts rapidement)
- ✅ Prototypage interface (placeholder images)
- ✅ Workshops/démos temps réel
- ❌ Production finale (préférer Qwen)

**Astuce**: Générer avec Turbo → Affiner avec Qwen (workflow hybride)

---

## API 3: Z-Image Turbo (Lumina-Next)

### 🎯 Présentation

**Z-Image Turbo** (basé sur l'architecture Lumina-Next-SFT) représente la nouvelle génération de modèles rapides :
- 🚀 **Architecture native Diffusers** : Intégration optimisée et robuste
- 🖼️ **Qualité photoréaliste** supérieure à SD XL Turbo
- ⚡ **Vitesse impressionnante** : 2-4 secondes pour une image HD
- 🔧 **Contrôle précis** : Respect strict du prompt

**Architecture**: ComfyUI + Diffusers Wrapper + Gemma 2B (Text Encoder)
**GPU**: RTX 3090 (24GB VRAM)
**Modèle**: Z-Image-Turbo (Safetensors, ~2.5GB) + Gemma-2-2B-It

### 🔗 Accès

- **Via ComfyUI** : Utilise le même endpoint que Qwen (`http://localhost:8188`)
- **Workflow** : `workflow_z_image_reboot.json`

### 💻 Exemple Python - Z-Image Turbo

```python
import json
from helpers.comfyui_client import create_client

# 1. Charger le workflow spécifique
# Note: Assurez-vous d'avoir le fichier JSON du workflow
with open('workflow_z_image_reboot.json', 'r') as f:
    workflow = json.load(f)

client = create_client("http://localhost:8188")

# 2. Configurer le prompt (Node ID 6 = CLIP Text Encode)
# Note: Les IDs peuvent varier selon le workflow, vérifiez le JSON
workflow["6"]["inputs"]["text"] = "A futuristic cityscape, cyberpunk style, neon lights, 8k, photorealistic"

# 3. Lancer la génération
try:
    print("🚀 Lancement de la génération Z-Image...")
    prompt_id = client.queue_prompt(workflow)
    images = client.wait_for_images(prompt_id)
    
    if images:
        images[0].save("z_image_cyberpunk.png")
        print("✅ Image sauvegardée : z_image_cyberpunk.png")
    else:
        print("❌ Aucune image générée")
except Exception as e:
    print(f"❌ Erreur : {e}")
```

---

## 📊 Comparaison Technique

### Tableau Récapitulatif

| Critère | Qwen Image-Edit | SD XL Turbo | Gagnant |
|---------|-----------------|-------------|---------|
| **Latence moyenne** | 5-10s | 1-3s | 🏆 Turbo |
| **Qualité visuelle** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 🏆 Qwen |
| **VRAM utilisée** | 10-15GB | 4-6GB | 🏆 Turbo |
| **Respect prompt** | Excellent | Bon | 🏆 Qwen |
| **Édition images** | ✅ Oui | ❌ Non | 🏆 Qwen |
| **Multilingue** | ✅ Oui | ⚠️ Limité | 🏆 Qwen |
| **Itérations/min** | 6-12 | 20-60 | 🏆 Turbo |
| **Apprentissage** | Moyen | Facile | 🏆 Turbo |

### Cas d'Usage Recommandés

#### Utilisez Qwen pour:
- 📚 **Projets académiques** nécessitant qualité
- 🎨 **Édition fine** d'images existantes
- 🌍 **Prompts multilingues** (français, etc.)
- 📊 **Visualisations** pour présentations
- 🔬 **Recherche** nécessitant reproductibilité

#### Utilisez SD XL Turbo pour:
- ⚡ **Brainstorming visuel** rapide
- 🎮 **Prototypes** applications
- 🏃 **Workshops** temps réel
- 🧪 **Tests A/B** multiples variations
- 🚀 **Démos** interactives

---

## 🚀 Exemples Pratiques

### Exemple 1: Workflow Hybride (Recommandé)

```python
# Phase 1: Exploration rapide avec Turbo (2 min)
concepts = [
    "minimalist logo design",
    "geometric abstract pattern",
    "nature-inspired organic shapes"
]

best_concepts = []
for concept in concepts:
    img = generate_image_turbo(f"professional {concept}", steps=6)
    # Évaluation humaine ou automatique
    best_concepts.append(img)

# Phase 2: Raffinement avec Qwen (10 min)
final_image = client.generate_text2image(
    prompt="professional minimalist logo design, clean lines, modern",
    steps=30,
    cfg_scale=7.5,
    width=1024,
    height=1024
)

print("✅ Workflow complet: exploration + raffinement")
```

### Exemple 2: Génération Dataset Éducatif

```python
# Créer dataset images pour classification
categories = {
    "animals": ["cat", "dog", "bird", "fish"],
    "vehicles": ["car", "bicycle", "airplane", "train"],
    "food": ["pizza", "burger", "salad", "pasta"]
}

dataset = []

for category, items in categories.items():
    for item in items:
        # Génération rapide avec Turbo
        img = generate_image_turbo(
            prompt=f"photo of a {item}, clear background, centered",
            steps=6
        )
        dataset.append({
            "category": category,
            "item": item,
            "image": img
        })

print(f"✅ Dataset de {len(dataset)} images créé en <5 min")
```

### Exemple 3: Comparaison Modèles (Recherche)

```python
import time

test_prompts = [
    "A serene landscape with mountains",
    "Abstract geometric pattern",
    "Portrait of a scientist"
]

results = []

for prompt in test_prompts:
    # Test Turbo
    start = time.time()
    img_turbo = generate_image_turbo(prompt, steps=6)
    time_turbo = time.time() - start
    
    # Test Qwen
    start = time.time()
    prompt_id = client.generate_text2image(prompt, steps=25)
    img_qwen = client.wait_for_images(prompt_id)[0]
    time_qwen = time.time() - start
    
    results.append({
        "prompt": prompt,
        "turbo_time": time_turbo,
        "qwen_time": time_qwen,
        "speedup": time_qwen / time_turbo
    })

# Analyse
import pandas as pd
df = pd.DataFrame(results)
print(df)
print(f"Speedup moyen: {df['speedup'].mean():.1f}x")
```

---

## 🔧 Troubleshooting

### Problèmes Communs

#### ❌ Erreur "Connection timeout" (Qwen)

```python
# Solution: Augmenter timeout
client = create_client(
    "https://qwen-image-edit.myia.io",
    timeout=60  # 60 secondes au lieu de 30
)
```

#### ❌ Erreur "Unauthorized" (SD XL Turbo)

```python
# Vérifier credentials
AUTH = ("votre_username", "votre_password")

# Tester connexion
response = requests.get(
    f"{BASE_URL}/sdapi/v1/sd-models",
    auth=AUTH
)
print(f"Status: {response.status_code}")  # Doit être 200
```

#### ❌ Images floues/artefacts (Les deux)

**Qwen**:
- Augmenter `steps` (30-40)
- Ajuster `cfg_scale` (6-8)
- Ajouter negative prompt détaillé

**Turbo**:
- Utiliser `steps=6` (ni trop bas ni trop haut)
- CFG entre 2.0-2.5
- Simplifier prompt (pas trop complexe)

#### ❌ "Out of memory" (VRAM)

**Qwen**:
- Réduire résolution (1024x1024 → 768x768)
- Attendre 30s entre générations

**Turbo**:
- Rare (modèle économe), vérifier autres processus GPU

### Bonnes Pratiques

1. **Gestion erreurs**:
```python
try:
    image = generate_image_turbo(prompt)
except Exception as e:
    print(f"Erreur: {e}")
    # Fallback ou retry
```

2. **Logging**:
```python
import logging
logging.basicConfig(level=logging.INFO)

logger = logging.getLogger(__name__)
logger.info(f"Génération: {prompt}")
```

3. **Rate limiting**:
```python
import time

# Éviter surcharge serveur
for prompt in prompts:
    image = generate_image_turbo(prompt)
    time.sleep(2)  # 2s entre requêtes
```

---

## 📚 Ressources Complémentaires

### Documentation Technique

- **Qwen Architecture**: [`docs/suivis/genai-image/phase-12-production/rapports/2025-10-16_12C_architectures-5-workflows-qwen.md`](../suivis/genai-image/phase-12a-production/rapports/2025-10-16_12C_architectures-5-workflows-qwen.md)
- **Tests Validation Qwen**: [`docs/suivis/genai-image/phase-12-production/rapports/2025-10-16_12B_RAPPORT-FINAL-TESTS-GENERATION.md`](../suivis/genai-image/phase-12a-production/rapports/2025-10-16_12B_RAPPORT-FINAL-TESTS-GENERATION.md)
- **Audit Infrastructure**: [`docs/suivis/genai-image/phase-14-audit-infrastructure/2025-10-16_AUDIT-INFRASTRUCTURE-COMPLETE.md`](../suivis/genai-image/phase-14-audit-infrastructure/2025-10-16_AUDIT-INFRASTRUCTURE-COMPLETE.md)

### Notebooks Jupyter

1. **Qwen - Tests Complets**:
   - Path: [`MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-5-ComfyUI-Local-Test.ipynb`](../../MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-5-ComfyUI-Local-Test.ipynb)
   - Contenu: Client Python, tests génération, workflows

2. **Applications Images** (à adapter):
   - Path: [`MyIA.AI.Notebooks/GenAI/04-Images-Applications/`](../../MyIA.AI.Notebooks/GenAI/04-Images-Applications/)
   - Exemples: Contenu éducatif, workflows créatifs

### Code Source

- **Client ComfyUI**: [`MyIA.AI.Notebooks/GenAI/shared/helpers/comfyui_client.py`](../../MyIA.AI.Notebooks/GenAI/shared/helpers/comfyui_client.py)
- **Tests**: [`MyIA.AI.Notebooks/GenAI/tests/test_comfyui_client.py`](../../MyIA.AI.Notebooks/GenAI/tests/test_comfyui_client.py)

### Liens Externes

- **Qwen Documentation**: [Qwen-VL GitHub](https://github.com/QwenLM/Qwen-VL)
- **ComfyUI**: [ComfyUI Documentation](https://github.com/comfyanonymous/ComfyUI)
- **Stable Diffusion**: [SD WebUI Forge](https://github.com/lllyasviel/stable-diffusion-webui-forge)
- **Automatic1111 API**: [SD API Wiki](https://github.com/AUTOMATIC1111/stable-diffusion-webui/wiki/API)

---

## 🎓 Support & Contact

### Assistance Technique

- **Documentation complète**: Ce guide + notebooks
- **Tests de validation**: Scripts Python fournis
- **Troubleshooting**: Section dédiée ci-dessus

### Contact Enseignant

Pour obtenir:
- 🔑 Credentials accès SD XL Turbo
- 💡 Conseils projets spécifiques
- 🐛 Support erreurs bloquantes
- 📊 Accès ressources supplémentaires

---

## 📝 Changelog

### Version 1.0 (2025-10-16)
- ✅ Documentation initiale complète
- ✅ Exemples Python Qwen + Turbo
- ✅ Comparaison technique détaillée
- ✅ Workflows pratiques recommandés
- ✅ Troubleshooting exhaustif

---

**Guide créé par**: Équipe CoursIA  
**Dernière mise à jour**: 2025-10-16  
**Validé pour**: Production étudiants Master IA

---

## 🚀 Quick Start (TL;DR)

```python
# QWEN (Qualité)
from helpers.comfyui_client import create_client
client = create_client("https://qwen-image-edit.myia.io")
img = client.generate_text2image("mountain sunset", steps=25)

# TURBO (Vitesse)
import requests
response = requests.post(
    "https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/txt2img",
    json={"prompt": "mountain sunset", "steps": 6},
    auth=("user", "pass")
)

# WORKFLOW HYBRIDE
# 1. Explorer avec Turbo (rapide)
# 2. Affiner avec Qwen (qualité)
```

**Bon développement! 🎨🚀**

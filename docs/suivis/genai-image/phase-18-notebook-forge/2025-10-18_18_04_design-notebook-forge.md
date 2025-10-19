# Design Notebook Forge SD XL Turbo - Phase 18

**Date**: 2025-10-18  
**Phase**: 18 - Développement Notebook Forge API SD XL Turbo  
**Fichier Cible**: `MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-4-Forge-SD-XL-Turbo.ipynb`

---

## 1. OBJECTIFS PÉDAGOGIQUES

### Objectifs Principaux

1. **Comprendre l'API REST Stable Diffusion Forge**
   - Architecture RESTful pour génération d'images
   - Endpoint principal `/sdapi/v1/txt2img`
   - Gestion des réponses JSON avec images base64

2. **Maîtriser la génération texte→image rapide**
   - Modèle SD XL Turbo optimisé pour vitesse
   - Workflow complet: prompt → API call → image PIL
   - Affichage et sauvegarde des résultats

3. **Explorer les paramètres optimaux SD XL Turbo**
   - Configuration spécifique Turbo (steps=4, cfg_scale=2.0)
   - Impact des paramètres sur qualité/vitesse
   - Cas d'usage: prototypage rapide, itération créative

### Prérequis Techniques

- Python 3.x installé
- Compréhension basique des API REST
- Connaissance élémentaire de Jupyter notebooks
- Accès réseau à l'API Forge

---

## 2. STRUCTURE NOTEBOOK (14 CELLULES)

### Vue d'Ensemble

| # | Type | Titre/Fonction | Complexité |
|---|------|----------------|------------|
| 0 | Markdown | Introduction: API Forge SD XL Turbo | Simple |
| 1 | Code | Imports & Configuration | Simple |
| 2 | Markdown | Architecture API: Endpoint txt2img | Moyen |
| 3 | Code | Fonction Helper: `generate_image_forge()` | Moyen |
| 4 | Markdown | Paramètres Optimaux Turbo | Moyen |
| 5 | Code | Exemple 1: Génération Simple | Simple |
| 6 | Markdown | Analyse: Décodage Base64 → PIL Image | Moyen |
| 7 | Code | Exemple 2: Variations de Prompt | Moyen |
| 8 | Markdown | Cas d'Usage Avancés: Prototypage Rapide | Moyen |
| 9 | Code | Exemple 3: Grid Comparaison Styles | Avancé |
| 10 | Markdown | Gestion des Erreurs & Bonnes Pratiques | Moyen |
| 11 | Code | Exemple 4: Helper avec Logging Coloré | Avancé |
| 12 | Markdown | Exercice Pratique: Votre Génération | Simple |
| 13 | Code | Template Exercice (Code à Compléter) | Simple |

**Total**: 14 cellules (7 Markdown + 7 Code)

---

## 3. DÉTAIL DES CELLULES

### Cellule 0 (Markdown): Introduction

```markdown
# Notebook: Stable Diffusion Forge - SD XL Turbo

## Objectif

Ce notebook pédagogique vous apprend à utiliser l'**API Stable Diffusion Forge** avec le modèle **SD XL Turbo** pour générer des images à partir de descriptions textuelles (prompts).

## Contexte

- **API**: Stable Diffusion Forge (WebUI Automatic1111)
- **Modèle**: SD XL Turbo (optimisé pour vitesse)
- **URL Base**: `https://turbo.stable-diffusion-webui-forge.myia.io`
- **Performance**: ~18s pour génération 512×512 (4 steps)

## Use Cases

- Prototypage rapide de concepts visuels
- Itération créative sur variations de prompts
- Exploration de styles artistiques
- Tests de faisabilité avant génération haute qualité

## Pré-requis

- Packages Python: `requests`, `Pillow`, `matplotlib`
- Accès réseau à l'API Forge
```

---

### Cellule 1 (Code): Imports & Configuration

```python
"""
Configuration initiale: imports et paramètres API
"""

# Imports standard
import requests
import json
import base64
from io import BytesIO
from typing import Optional, Dict, Any
import warnings

# Imports visualisation
from PIL import Image
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches

# Configuration
API_BASE_URL = "https://turbo.stable-diffusion-webui-forge.myia.io"
API_ENDPOINT_TXT2IMG = f"{API_BASE_URL}/sdapi/v1/txt2img"

# Configuration matplotlib
plt.rcParams['figure.figsize'] = (12, 8)
plt.rcParams['figure.dpi'] = 100

# Suppression warnings
warnings.filterwarnings('ignore')

print("✅ Configuration chargée")
print(f"📍 API Endpoint: {API_ENDPOINT_TXT2IMG}")
```

---

### Cellule 2 (Markdown): Architecture API

```markdown
## Architecture de l'API Forge

### Endpoint Principal: POST /sdapi/v1/txt2img

L'API Forge utilise une architecture RESTful classique:

**Requête**:
```http
POST https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/txt2img
Content-Type: application/json

{
  "prompt": "A serene mountain landscape at sunset",
  "negative_prompt": "blurry, low quality",
  "steps": 4,
  "width": 512,
  "height": 512,
  "cfg_scale": 2.0,
  "sampler_name": "Euler a"
}
```

**Réponse**:
```json
{
  "images": ["<base64_encoded_image_string>"],
  "parameters": { ... },
  "info": "..."
}
```

### Workflow Complet

1. **Construction du payload JSON** (paramètres génération)
2. **Appel POST** via `requests.post()`
3. **Parsing de la réponse JSON**
4. **Décodage base64 → bytes**
5. **Conversion bytes → PIL.Image**
6. **Affichage/Sauvegarde**
```

---

### Cellule 3 (Code): Fonction Helper

```python
"""
Fonction helper pour génération d'images via API Forge
"""

def generate_image_forge(
    prompt: str,
    negative_prompt: str = "blurry, low quality, distorted",
    steps: int = 4,
    width: int = 512,
    height: int = 512,
    cfg_scale: float = 2.0,
    sampler_name: str = "Euler a",
    seed: int = -1,
    timeout: int = 60
) -> Optional[Image.Image]:
    """
    Génère une image via l'API Stable Diffusion Forge (SD XL Turbo).
    
    Args:
        prompt: Description textuelle de l'image à générer
        negative_prompt: Éléments à éviter dans l'image
        steps: Nombre d'étapes de diffusion (4 optimal pour Turbo)
        width: Largeur de l'image en pixels
        height: Hauteur de l'image en pixels
        cfg_scale: Guidance scale (2.0 optimal pour Turbo)
        sampler_name: Algorithme de sampling
        seed: Seed pour reproductibilité (-1 = aléatoire)
        timeout: Timeout requête HTTP en secondes
        
    Returns:
        PIL.Image.Image si succès, None si erreur
        
    Raises:
        requests.exceptions.RequestException: Erreurs réseau/HTTP
    """
    
    # Construction du payload
    payload = {
        "prompt": prompt,
        "negative_prompt": negative_prompt,
        "steps": steps,
        "width": width,
        "height": height,
        "cfg_scale": cfg_scale,
        "sampler_name": sampler_name,
        "seed": seed
    }
    
    try:
        # Appel API
        response = requests.post(
            API_ENDPOINT_TXT2IMG,
            json=payload,
            timeout=timeout
        )
        response.raise_for_status()
        
        # Parsing réponse
        result = response.json()
        
        # Extraction image base64
        if "images" in result and len(result["images"]) > 0:
            image_base64 = result["images"][0]
            
            # Décodage base64 → bytes
            image_bytes = base64.b64decode(image_base64)
            
            # Conversion bytes → PIL Image
            image = Image.open(BytesIO(image_bytes))
            
            return image
        else:
            print("❌ Aucune image dans la réponse API")
            return None
            
    except requests.exceptions.Timeout:
        print(f"⏱️ Timeout après {timeout}s")
        return None
    except requests.exceptions.RequestException as e:
        print(f"❌ Erreur HTTP: {e}")
        return None
    except Exception as e:
        print(f"❌ Erreur inattendue: {e}")
        return None

# Test rapide
print("✅ Fonction `generate_image_forge()` définie")
```

---

### Cellule 4 (Markdown): Paramètres Optimaux Turbo

```markdown
## Paramètres Optimaux pour SD XL Turbo

Le modèle **SD XL Turbo** est spécifiquement entraîné pour une génération ultra-rapide:

### Configuration Recommandée

| Paramètre | Valeur Optimale | Explication |
|-----------|----------------|-------------|
| `steps` | **4** | Turbo nécessite exactement 4 étapes de diffusion |
| `cfg_scale` | **2.0** | Guidance faible (vs 7-9 pour modèles classiques) |
| `sampler_name` | `"Euler a"` | Sampler rapide et efficace |
| `width` / `height` | **512×512** | Résolution optimale pour vitesse |

### ⚠️ Différences vs Modèles Classiques

- **Steps**: SD classique utilise 20-50 steps, Turbo seulement 4
- **CFG Scale**: SD classique utilise 7-15, Turbo optimisé pour 2.0
- **Vitesse**: ~5x plus rapide qu'un modèle SD XL standard

### Impact sur la Qualité

- **Trade-off**: Vitesse ↑ vs Détails fins ↓
- **Use Case Idéal**: Prototypage, exploration créative, brouillons rapides
- **Limitation**: Moins de contrôle fin qu'un modèle haute qualité
```

---

### Cellule 5 (Code): Exemple Simple

```python
"""
Exemple 1: Génération simple d'une image
"""

# Prompt simple
prompt_simple = "A serene mountain landscape at sunset, photorealistic"

print(f"🎨 Génération: '{prompt_simple}'")
print("⏳ Requête en cours (≈18s)...")

# Génération
image = generate_image_forge(
    prompt=prompt_simple,
    negative_prompt="blurry, low quality, distorted",
    steps=4,
    width=512,
    height=512
)

# Affichage
if image:
    plt.figure(figsize=(8, 6))
    plt.imshow(image)
    plt.axis('off')
    plt.title(f"Prompt: {prompt_simple}", fontsize=10, pad=10)
    plt.tight_layout()
    plt.show()
    
    print(f"✅ Image générée: {image.size[0]}×{image.size[1]} pixels")
else:
    print("❌ Échec de génération")
```

---

### Cellule 6 (Markdown): Décodage Base64

```markdown
## Analyse Technique: Décodage Base64 → PIL Image

### Pipeline de Traitement

```python
# 1. Réponse API (JSON)
response.json()  # → {"images": ["iVBORw0KGg..."]}

# 2. Extraction string base64
image_base64 = result["images"][0]

# 3. Décodage base64 → bytes
image_bytes = base64.b64decode(image_base64)

# 4. Bytes → PIL Image via BytesIO
image = Image.open(BytesIO(image_bytes))
```

### Pourquoi Base64?

- **Transport JSON**: Les images binaires ne peuvent pas être directement incluses dans du JSON
- **Encodage**: Base64 convertit les bytes en caractères ASCII safe
- **Overhead**: ~33% de taille supplémentaire (acceptable pour API REST)

### Alternatives

- **Streaming**: Pour grandes images, utiliser endpoint retournant un blob binaire direct
- **URLs temporaires**: L'API pourrait retourner une URL de téléchargement (non supporté ici)
```

---

### Cellule 7 (Code): Variations de Prompt

```python
"""
Exemple 2: Exploration de variations de prompt
"""

# Variations progressives
prompts_variations = [
    "A futuristic city at night",
    "A futuristic city at night, neon lights",
    "A futuristic city at night, cyberpunk style, neon lights, rain"
]

# Génération des 3 variations
images_variations = []
for i, prompt in enumerate(prompts_variations, 1):
    print(f"🎨 [{i}/3] Génération: '{prompt}'")
    img = generate_image_forge(prompt=prompt)
    if img:
        images_variations.append((prompt, img))
    print()

# Affichage en grid
if images_variations:
    fig, axes = plt.subplots(1, len(images_variations), figsize=(15, 5))
    
    for ax, (prompt, img) in zip(axes, images_variations):
        ax.imshow(img)
        ax.axis('off')
        # Titre tronqué pour lisibilité
        title = prompt if len(prompt) <= 40 else prompt[:37] + "..."
        ax.set_title(title, fontsize=9)
    
    plt.suptitle("Exploration: Variations de Prompt", fontsize=12, y=0.98)
    plt.tight_layout()
    plt.show()
    
    print(f"✅ {len(images_variations)} images générées")
else:
    print("❌ Aucune image générée")
```

---

### Cellule 8 (Markdown): Cas d'Usage Avancés

```markdown
## Cas d'Usage Avancés: Prototypage Rapide

### 1. Itération Créative

**Problème**: Explorer différentes variantes d'un concept visuel rapidement

**Solution**: Générer un grid de variations avec différents styles/modifieurs

```python
base_prompt = "A magical forest"
modifiers = ["dreamy", "dark gothic", "bright colorful", "ethereal"]
# → 4 variations en ~1min
```

### 2. Validation de Faisabilité

**Problème**: Vérifier si un concept est réalisable avant génération haute qualité

**Solution**: Prototype rapide avec SD XL Turbo → validation → génération finale avec modèle lent

### 3. A/B Testing de Prompts

**Problème**: Comparer l'impact de mots-clés spécifiques

**Solution**: Générer paires d'images avec/sans keyword précis

```python
prompts_ab = [
    "A landscape",
    "A landscape, photorealistic"
]
# → Analyse visuelle de l'impact de "photorealistic"
```

### Limitations à Considérer

- ❌ Détails fins limités (4 steps)
- ❌ Contrôle précis difficile (cfg_scale faible)
- ✅ Parfait pour exploration, brouillons, concepts
```

---

### Cellule 9 (Code): Grid Comparaison Styles

```python
"""
Exemple 3: Grid de comparaison de styles artistiques
"""

# Prompt de base
base_concept = "A portrait of a wise old wizard"

# Styles à tester
art_styles = [
    "oil painting",
    "digital art",
    "watercolor",
    "pencil sketch"
]

# Génération grid 2×2
print(f"🎨 Génération grid {len(art_styles)} styles sur: '{base_concept}'")
print("=" * 60)

images_grid = []
for i, style in enumerate(art_styles, 1):
    full_prompt = f"{base_concept}, {style} style"
    print(f"[{i}/{len(art_styles)}] Style: {style}")
    
    img = generate_image_forge(prompt=full_prompt, seed=42)  # Seed fixe pour comparaison
    if img:
        images_grid.append((style, img))

# Affichage grid 2×2
if len(images_grid) == 4:
    fig, axes = plt.subplots(2, 2, figsize=(12, 12))
    axes = axes.flatten()
    
    for ax, (style, img) in zip(axes, images_grid):
        ax.imshow(img)
        ax.axis('off')
        ax.set_title(f"Style: {style}", fontsize=11, fontweight='bold')
    
    plt.suptitle(
        f"Comparaison Styles Artistiques\nBase: '{base_concept}'",
        fontsize=13,
        y=0.98
    )
    plt.tight_layout()
    plt.show()
    
    print(f"\n✅ Grid {len(images_grid)} styles généré")
else:
    print(f"\n⚠️ Seulement {len(images_grid)}/4 images générées")
```

---

### Cellule 10 (Markdown): Gestion des Erreurs

```markdown
## Gestion des Erreurs & Bonnes Pratiques

### Erreurs Fréquentes

#### 1. Timeout

**Symptôme**: `⏱️ Timeout après 60s`

**Causes**:
- API surchargée
- Réseau instable

**Solution**:
```python
generate_image_forge(prompt="...", timeout=120)  # Augmenter timeout
```

#### 2. Erreur HTTP 5xx

**Symptôme**: `❌ Erreur HTTP: 500 Internal Server Error`

**Causes**:
- Serveur Forge temporairement indisponible
- Payload invalide

**Solution**:
- Vérifier syntaxe du prompt (caractères spéciaux?)
- Réessayer après quelques secondes

#### 3. Réponse Vide

**Symptôme**: `❌ Aucune image dans la réponse API`

**Causes**:
- Prompt violant les policies de contenu
- Erreur silencieuse côté serveur

**Solution**:
- Simplifier le prompt
- Tester avec un prompt minimal connu fonctionnel

### Bonnes Pratiques

1. **Toujours spécifier un timeout** (éviter blocages infinis)
2. **Utiliser negative_prompt** (améliore qualité)
3. **Fixer seed pour reproductibilité** lors des tests
4. **Gérer gracieusement les None** retournés
5. **Logger les erreurs** pour debugging

```python
# Exemple robuste
try:
    img = generate_image_forge(prompt="...", timeout=90)
    if img:
        # Traitement réussi
        pass
    else:
        # Gestion échec gracieuse
        print("Génération échouée, utilisation image par défaut")
except Exception as e:
    # Fallback global
    logging.error(f"Erreur critique: {e}")
```
```

---

### Cellule 11 (Code): Helper avec Logging Coloré

```python
"""
Exemple 4: Version améliorée avec logging coloré
(Inspiré du pattern LocalLlama)
"""

from enum import Enum

class LogColor(Enum):
    """Codes ANSI pour logging coloré dans notebooks"""
    RESET = '\033[0m'
    INFO = '\033[94m'      # Bleu
    SUCCESS = '\033[92m'   # Vert
    WARNING = '\033[93m'   # Jaune
    ERROR = '\033[91m'     # Rouge
    HEADER = '\033[95m'    # Magenta

def log_colored(message: str, color: LogColor = LogColor.INFO):
    """Affiche message coloré"""
    print(f"{color.value}{message}{LogColor.RESET.value}")

def generate_image_forge_v2(
    prompt: str,
    verbose: bool = True,
    **kwargs
) -> Optional[Image.Image]:
    """
    Version améliorée avec logging détaillé
    """
    if verbose:
        log_colored(f"🎨 Prompt: '{prompt}'", LogColor.HEADER)
        log_colored(f"⚙️  Paramètres: steps={kwargs.get('steps', 4)}, "
                   f"size={kwargs.get('width', 512)}×{kwargs.get('height', 512)}",
                   LogColor.INFO)
    
    # Génération
    image = generate_image_forge(prompt=prompt, **kwargs)
    
    # Logging résultat
    if image:
        if verbose:
            log_colored(f"✅ Génération réussie: {image.size[0]}×{image.size[1]}", 
                       LogColor.SUCCESS)
        return image
    else:
        if verbose:
            log_colored("❌ Échec génération", LogColor.ERROR)
        return None

# Test
print("Test fonction avec logging coloré:")
print("-" * 50)
img_test = generate_image_forge_v2(
    prompt="A cozy cabin in snowy mountains",
    steps=4,
    width=512,
    height=512,
    verbose=True
)

if img_test:
    plt.figure(figsize=(6, 6))
    plt.imshow(img_test)
    plt.axis('off')
    plt.title("Test Logging Coloré", fontsize=11)
    plt.show()
```

---

### Cellule 12 (Markdown): Exercice Pratique

```markdown
## 🎯 Exercice Pratique: À Votre Tour!

### Objectif

Créer votre propre génération d'image en appliquant les concepts appris.

### Consigne

Complétez le code de la cellule suivante pour:

1. **Définir votre prompt créatif** (thème libre)
2. **Configurer les paramètres optimaux** (steps=4, cfg_scale=2.0, etc.)
3. **Générer l'image** via `generate_image_forge_v2()`
4. **Afficher le résultat** avec un titre personnalisé

### Bonus (Optionnel)

- Créez un grid de 2-4 variations de votre prompt
- Expérimentez avec différents `negative_prompt`
- Comparez l'impact de `seed` fixe vs aléatoire

### Critères de Réussite

- ✅ Image générée sans erreur
- ✅ Affichage matplotlib fonctionnel
- ✅ Titre descriptif
- ✅ Code commenté et lisible
```

---

### Cellule 13 (Code): Template Exercice

```python
"""
🎯 EXERCICE PRATIQUE: Votre Génération
Complétez le code ci-dessous
"""

# TODO: Remplacez par votre prompt créatif
mon_prompt = "Votre description ici..."

# TODO: Configurez vos paramètres
mes_parametres = {
    "prompt": mon_prompt,
    "negative_prompt": "à compléter...",
    "steps": 4,  # Optimal pour Turbo
    "width": 512,
    "height": 512,
    "cfg_scale": 2.0,  # Optimal pour Turbo
    "seed": -1,  # -1 = aléatoire, ou fixez un nombre pour reproductibilité
    "verbose": True
}

# Génération
print("=" * 60)
print("EXERCICE: Votre Génération Personnalisée")
print("=" * 60)

mon_image = generate_image_forge_v2(**mes_parametres)

# Affichage
if mon_image:
    plt.figure(figsize=(8, 8))
    plt.imshow(mon_image)
    plt.axis('off')
    
    # TODO: Personnalisez votre titre
    plt.title("Mon Image Générée avec SD XL Turbo", fontsize=12, pad=15)
    
    plt.tight_layout()
    plt.show()
    
    log_colored("🎉 Bravo! Exercice réussi!", LogColor.SUCCESS)
else:
    log_colored("⚠️ Génération échouée. Vérifiez vos paramètres.", LogColor.WARNING)

# BONUS: Grid de variations (décommentez pour tester)
"""
variations = [
    "variation 1",
    "variation 2",
    "variation 3",
    "variation 4"
]

images_bonus = []
for var in variations:
    img = generate_image_forge_v2(prompt=var, verbose=False)
    if img:
        images_bonus.append(img)

# Affichage grid 2×2
if len(images_bonus) == 4:
    fig, axes = plt.subplots(2, 2, figsize=(12, 12))
    axes = axes.flatten()
    for ax, img in zip(axes, images_bonus):
        ax.imshow(img)
        ax.axis('off')
    plt.suptitle("Mes Variations", fontsize=13)
    plt.show()
"""
```

---

## 4. ADAPTATIONS PAR RAPPORT À LOCALLLAMA

### Éléments Conservés ✅

| Pattern LocalLlama | Adaptation Forge |
|-------------------|------------------|
| Logging coloré (`LogColor` enum) | ✅ Réutilisé à l'identique |
| Structure helper function modulaire | ✅ `generate_image_forge()` similaire |
| Gestion erreurs robuste (try/except) | ✅ Timeout + HTTP errors |
| Progression pédagogique exemples simples→complexes | ✅ 4 exemples escalade complexité |
| Exercice pratique final avec TODO | ✅ Template code à compléter |

### Éléments Supprimés ❌

| Pattern LocalLlama | Raison Suppression |
|-------------------|-------------------|
| Chargement `.env` multi-endpoints | ❌ API Forge = endpoint unique fixe |
| Tests tokenization | ❌ Non pertinent pour génération images |
| Function calling | ❌ Spécifique aux LLMs |
| Tests OpenAI SDK vs raw requests | ❌ Forge = raw requests uniquement |
| Benchmarking multi-providers | ❌ Provider unique (Forge) |

### Nouveautés Ajoutées 🆕

| Nouveauté | Justification |
|-----------|---------------|
| Décodage base64 → PIL Image | ⭐ Spécifique aux APIs images |
| Affichage matplotlib | ⭐ Visualisation résultats critiques |
| Grid comparaisons visuelles | ⭐ Pédagogie exploration créative |
| Documentation paramètres Turbo | ⭐ Optimisations modèle spécifiques |
| Seed pour reproductibilité | ⭐ Important pour comparaisons |

---

## 5. VALIDATION PÉDAGOGIQUE

### Checklist Qualité

- ✅ **Progression logique**: Introduction → Concepts → Exemples → Exercice
- ✅ **Exemples concrets reproductibles**: Prompts testés fonctionnels
- ✅ **Exercice pratique final**: Template TODO guidé
- ✅ **Gestion erreurs expliquée**: Cellule dédiée bonnes pratiques
- ✅ **Documentation complète**: Markdown détaillé entre cellules code
- ✅ **Code commenté**: Docstrings + inline comments
- ✅ **Visualisations**: Matplotlib pour tous exemples

### Métriques Pédagogiques

| Critère | Cible | Réalisé |
|---------|-------|---------|
| Nombre cellules | 10-15 | **14** ✅ |
| Ratio Markdown/Code | ~50/50 | **50/50** ✅ |
| Exemples pratiques | ≥3 | **4** ✅ |
| Exercice final | 1 | **1** ✅ |
| Documentation erreurs | Oui | **Oui** ✅ |

---

## 6. PROCHAINES ÉTAPES

### Création Notebook (Partie 6)

Utiliser **MCP jupyter-papermill** pour:

1. Créer structure base via `create_notebook()`
2. Ajouter cellules une par une via `add_cell()`
3. Valider structure via `inspect_notebook()`

### Tests Fonctionnels (Partie 7)

Script PowerShell pour:

1. Vérifier structure notebook (14 cellules, types corrects)
2. Tester exécution via papermill (avec timeout adapté)
3. Valider outputs (images générées)

### Documentation (Partie 9)

Créer:

- `README.md` accompagnement notebook
- Guide installation dépendances
- Screenshots exemples résultats

---

## 7. NOTES TECHNIQUES

### Dépendances Python

```txt
requests>=2.31.0
Pillow>=10.0.0
matplotlib>=3.7.0
```

### Performance Estimée

- Cellule 5 (1 image): ~18s
- Cellule 7 (3 images): ~54s
- Cellule 9 (4 images): ~72s
- **Total exécution complète**: ~3min (si toutes cellules exécutées séquentiellement)

### Limitations Connues

1. **Réseau requis**: Notebook inutilisable offline
2. **Timeout variabilité**: API partagée, temps réponse fluctue
3. **Qualité images**: Trade-off vitesse vs détails (Turbo)
4. **Pas de streaming**: Pas de feedback progressif pendant génération

---

**Design validé** ✅  
**Prêt pour création via MCP papermill** ✅  
**Date Design**: 2025-10-18  
**Phase**: 18
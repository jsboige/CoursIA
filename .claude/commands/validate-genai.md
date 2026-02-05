# Validate GenAI Stack Command

Valide la stack GenAI complète (services, authentification, modèles, notebooks).

## Usage

```
/validate-genai [target] [options]
```

## Arguments

- `target`: Cible de validation (par défaut: all)
  - `all`: Validation complète
  - `services`: Services Docker uniquement
  - `auth`: Authentification ComfyUI
  - `models`: Modèles disponibles
  - `notebooks`: Notebooks GenAI
  - `vram`: Vérification GPU/VRAM

- Options:
  - `--local`: Utiliser les services Docker locaux (LOCAL_MODE=true)
  - `--remote`: Utiliser les services myia.io (LOCAL_MODE=false)
  - `--quick`: Validation rapide sans génération d'images
  - `--verbose`: Affichage détaillé

## Scripts disponibles

Les scripts de validation sont dans `scripts/genai-stack/` :

| Script | Description | Usage |
|--------|-------------|-------|
| `validate_stack.py` | Validation complète ComfyUI | `python scripts/genai-stack/validate_stack.py` |
| `validate_notebooks.py` | Validation notebooks Papermill | `python scripts/genai-stack/validate_notebooks.py` |
| `check_vram.py` | Vérification GPU/VRAM | `python scripts/genai-stack/check_vram.py` |
| `list_models.py` | Liste des modèles disponibles | `python scripts/genai-stack/list_models.py` |
| `list_nodes.py` | Liste des nodes ComfyUI | `python scripts/genai-stack/list_nodes.py` |

## Instructions pour Claude

### 1. Déterminer le mode (local vs remote)

```python
# Lire .env pour déterminer LOCAL_MODE
env_path = "MyIA.AI.Notebooks/GenAI/.env"
if file_exists(env_path):
    local_mode = grep("LOCAL_MODE=true", env_path)
else:
    local_mode = False  # Default: remote (myia.io)
```

### 2. Validation selon la cible

#### Target: services

```bash
# Vérifier les services Docker locaux
python scripts/genai-stack/validate_stack.py --services-only

# Ou vérifier la connectivité remote
curl -s https://qwen-image-edit.myia.io/health
curl -s https://z-image.myia.io/health
```

#### Target: auth

```bash
# Tester l'authentification ComfyUI
python scripts/genai-stack/validate_stack.py --auth-only
```

Vérifier que `COMFYUI_AUTH_TOKEN` est configuré dans `.env`.

#### Target: models

```bash
# Lister les modèles disponibles
python scripts/genai-stack/list_models.py
python scripts/genai-stack/list_nodes.py
```

#### Target: vram

```bash
# Vérifier GPU et VRAM disponibles
python scripts/genai-stack/check_vram.py
```

Requis: ~29GB VRAM pour Qwen Image Edit, ~10GB pour Z-Image.

#### Target: notebooks

```bash
# Valider les notebooks GenAI
python scripts/genai-stack/validate_notebooks.py MyIA.AI.Notebooks/GenAI/Image/01-Foundation
```

### 3. Mapping notebooks -> services requis

```python
NOTEBOOK_SERVICE_MAP = {
    "cloud": ["01-1-*.ipynb", "01-3-*.ipynb"],      # OpenAI DALL-E (cloud)
    "forge": ["01-4-*.ipynb", "02-3-*.ipynb"],      # SD Forge
    "qwen": ["01-5-*.ipynb", "02-1-*.ipynb"],       # ComfyUI Qwen
    "zimage": ["02-4-*.ipynb"],                      # Z-Image/vLLM
    "multi": ["03-*.ipynb"],                         # Multi-modèles
    "apps": ["04-*.ipynb"]                           # Applications
}
```

### 4. Rapport de validation

```markdown
=== GenAI Stack Validation Report ===
Date: {timestamp}
Mode: {local|remote}

--- Services ---
[OK] ComfyUI: https://qwen-image-edit.myia.io (200 OK)
[OK] Z-Image: https://z-image.myia.io (200 OK)
[OK] SD Forge: https://stable-diffusion-webui-forge.myia.io (200 OK)

--- Authentication ---
[OK] COMFYUI_AUTH_TOKEN: Configured
[OK] Bearer token validation: Success

--- GPU/VRAM ---
[OK] GPU: NVIDIA RTX 3090
[OK] VRAM: 24GB available
[WARN] Qwen Image Edit requires 29GB - may need model switching

--- Models ---
[OK] qwen_image_edit_2509_fp8: Loaded
[OK] qwen_image_vae: Loaded
[OK] z-image-turbo: Available

--- Notebooks ---
[OK] 01-Foundation: 5/5 ready
[WARN] 02-Advanced: Requires local GPU services
[OK] 03-Orchestration: 3/3 ready
[OK] 04-Applications: 4/4 ready

=== Summary ===
Status: READY (with warnings)
Recommended: Use --remote for 01-Foundation, local Docker for 02-Advanced
```

## Exemples

```
/validate-genai all
/validate-genai services --local
/validate-genai notebooks --quick
/validate-genai auth --verbose
/validate-genai vram
```

## Configuration requise

### Fichier .env

```bash
# MyIA.AI.Notebooks/GenAI/.env
LOCAL_MODE=false  # true pour Docker local

# Services myia.io
COMFYUI_API_URL=https://qwen-image-edit.myia.io
COMFYUI_AUTH_TOKEN=your_bearer_token_here
ZIMAGE_API_URL=https://z-image.myia.io

# Ou services locaux
# COMFYUI_API_URL=http://localhost:8188
# ZIMAGE_API_URL=http://localhost:8001
```

### Docker local (si LOCAL_MODE=true)

```bash
cd docker-configurations/services/comfyui-qwen
docker-compose up -d
```

## Dépendances

- Python 3.10+
- requests, python-dotenv
- GPU NVIDIA avec CUDA (pour exécution locale)
- Docker (pour services locaux)

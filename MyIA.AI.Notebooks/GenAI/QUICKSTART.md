# GenAI - Guide de Demarrage Rapide

## Configuration en 2 minutes (Mode Remote - Etudiants)

> **Note** : Ce guide est pour le **mode REMOTE** - vous utilisez les services heberges par l'enseignant via myia.io. Pas besoin de GPU local.

### Etape 1 : Copier la configuration

```bash
cd MyIA.AI.Notebooks/GenAI
cp .env.example .env
```

### Etape 2 : Configurer les tokens

Ouvrez le fichier `.env` et configurez :

```bash
# Mode Remote (par defaut) - NE PAS MODIFIER
LOCAL_MODE=false

# Token ComfyUI (fourni par l'enseignant) - format bcrypt $2b$12$...
COMFYUI_API_TOKEN=<token_fourni>
COMFYUI_AUTH_TOKEN=<token_fourni>
QWEN_API_TOKEN=<token_fourni>

# OpenRouter (gratuit - creer compte sur https://openrouter.ai)
OPENROUTER_API_KEY=<votre_cle_openrouter>
# OU utiliser la cle cours si fournie
OPENAI_API_KEY=<cle_cours_ou_openrouter>
OPENAI_BASE_URL=https://openrouter.ai/api/v1
```

### Etape 3 : Tester la connexion aux services

```bash
# Test rapide des services myia.io (curl)
curl -s -w "\n%{http_code}" "https://qwen-image-edit.myia.io/" | tail -1
curl -s -w "\n%{http_code}" "https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/options" | tail -1
curl -s -w "\n%{http_code}" "https://z-image.myia.io/health" | tail -1
# Reponse attendue : 200 (ou 401 pour ComfyUI si token requis)
```

**Note** : Les scripts `scripts/genai-stack/validate_*.py` sont concus pour le mode LOCAL uniquement.

---

## Services Disponibles (Fevrier 2026)

| Service | URL | Status | Notebooks |
| ------- | --- | ------ | --------- |
| **ComfyUI Qwen** | `https://qwen-image-edit.myia.io` | Actif | 01-5, 02-1 |
| **SD Forge Turbo** | `https://turbo.stable-diffusion-webui-forge.myia.io` | Actif | 01-4, 02-3 |
| **Z-Image Lumina** | `https://z-image.myia.io` | Actif | 02-4 |
| **OpenRouter** | `https://openrouter.ai/api/v1` | Actif | 01-1, 01-2, 01-3 |

### Test rapide des services

```bash
# ComfyUI Qwen
curl -s -w "%{http_code}" "https://qwen-image-edit.myia.io/system_stats" \
  -H "Authorization: Bearer <VOTRE_TOKEN>"

# SD Forge Turbo
curl -s -w "%{http_code}" "https://turbo.stable-diffusion-webui-forge.myia.io/sdapi/v1/options"

# Z-Image
curl -s -w "%{http_code}" "https://z-image.myia.io/health"
```

---

## Notebooks par Service

### OpenRouter (LLMs - gratuit)

- `01-1-OpenAI-DALL-E-3.ipynb` - Generation d'images via API
- `01-2-GPT-5-Image-Generation.ipynb` - Vision multimodale
- `01-3-Basic-Image-Operations.ipynb` - Operations de base

**Config requise :**

```bash
OPENAI_API_KEY=sk-or-v1-...
OPENAI_BASE_URL=https://openrouter.ai/api/v1
OPENAI_CHAT_MODEL_ID=meta-llama/llama-3.2-3b-instruct:free
```

### SD Forge Turbo (SDXL)

- `01-4-Forge-SD-XL-Turbo.ipynb` - Generation rapide SDXL
- `02-3-Stable-Diffusion-3-5.ipynb` - SD avance

**Config requise :**

```bash
FORGE_API_URL=https://turbo.stable-diffusion-webui-forge.myia.io
```

### ComfyUI Qwen (Edition d'images)

- `01-5-Qwen-Image-Edit.ipynb` - Introduction Qwen
- `02-1-Qwen-Image-Edit-2509.ipynb` - Edition avancee

**Config requise :**

```bash
COMFYUI_API_URL=https://qwen-image-edit.myia.io
COMFYUI_AUTH_TOKEN=<token_fourni>
```

### Z-Image Lumina (Text-to-Image)

- `02-4-Z-Image-Lumina2.ipynb` - Generation haute qualite

**Config requise :**

```bash
ZIMAGE_API_URL=https://z-image.myia.io
```

---

## Depannage

### Erreur 401 Unauthorized (ComfyUI)

- Verifiez que le token est correct dans `.env`
- Le token doit commencer par `$2b$12$...` (hash bcrypt)

### Erreur de connexion

- Verifiez votre connexion internet
- Les services myia.io sont accessibles depuis l'exterieur

### Module not found

```bash
pip install python-dotenv requests pillow openai
```

### Variable d'environnement non trouvee

- Verifiez que le fichier `.env` existe dans `MyIA.AI.Notebooks/GenAI/`
- Relancez le kernel Jupyter apres modification du `.env`

---

## Mode Local (Deploiement Docker)

Si vous souhaitez deployer les services sur votre propre machine (GPU requis) :

1. Consultez le notebook `00-GenAI-Environment/00-6-Local-Docker-Deployment.ipynb`
2. Configurez `LOCAL_MODE=true` dans `.env`
3. Les URLs basculent automatiquement vers localhost

**Prerequis mode local :**

- Docker Desktop avec support GPU NVIDIA
- GPU avec 8-20GB+ VRAM selon le service
- NVIDIA Driver >= 535.x

---

## Pour aller plus loin

- **Documentation complete** : [README.md](README.md)
- **Deploiement local** : `00-GenAI-Environment/00-6-Local-Docker-Deployment.ipynb`
- **Validation stack locale** : `python scripts/genai-stack/validate_stack.py`

---

## Contact

En cas de probleme persistant, contacter l'enseignant avec :

1. Le message d'erreur complet
2. Le notebook concerne
3. Le resultat des tests curl ci-dessus

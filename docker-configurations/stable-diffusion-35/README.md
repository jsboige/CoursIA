# Stable Diffusion 3.5 Service

## 📋 Description

Service de génération d'images basé sur Stable Diffusion 3.5 Large.
Optimisé pour la génération polyvalente production avec API FastAPI.

## 🎯 Rôle du Service

- Génération d'images polyvalente haute qualité
- API REST FastAPI performante
- Support multi-résolutions et styles
- Interface optimisée pour intégration production

## 📁 Structure des Fichiers

```
stable-diffusion-35/
├── config/
│   └── config.json               # Configuration du modèle et API
├── models/                       # Cache des modèles Hugging Face
│   └── (téléchargement auto depuis HF)
└── README.md                     # Ce fichier
```

## 📦 Modèles

### Téléchargement Automatique

Le modèle **Stable Diffusion 3.5 Large** est téléchargé automatiquement depuis Hugging Face au premier démarrage.

- **Modèle**: `stabilityai/stable-diffusion-3.5-large`
- **Taille**: ~6.9 GB
- **Cache**: `/models` dans le container
- **Source**: https://huggingface.co/stabilityai/stable-diffusion-3.5-large

⚠️ **Token Hugging Face**: Peut nécessiter un token HF si modèle privé/gated.

### Configuration Token HF (si nécessaire)

```bash
# Ajouter dans .env.docker
HUGGINGFACE_TOKEN=hf_xxxxxxxxxxxxxxxxxxxx
```

## 🔧 Configuration

### Fichier `config/config.json`

```json
{
  "model_id": "stabilityai/stable-diffusion-3.5-large",
  "torch_dtype": "float16",
  "device": "cuda",
  "cache_dir": "/models",
  "generation_defaults": {
    "num_inference_steps": 50,
    "guidance_scale": 7.5,
    "width": 1024,
    "height": 1024
  }
}
```

### Variables d'Environnement Docker

- `CUDA_VISIBLE_DEVICES=0` : GPU à utiliser
- `MODEL_NAME` : Nom du modèle HuggingFace
- `CACHE_DIR` : Répertoire de cache des modèles
- `TORCH_COMPILE=1` : Active compilation PyTorch (perf++)

## 🚀 Utilisation

### Démarrage du Service

```powershell
# Via docker-compose principal
docker compose up stable-diffusion-35 -d

# Suivre le téléchargement du modèle (premier démarrage)
docker compose logs -f stable-diffusion-35
```

### Accès à l'API

- **API Endpoint**: http://localhost:8190
- **Health Check**: http://localhost:8190/health
- **Documentation API**: http://localhost:8190/docs (Swagger UI)

### Exemple d'Utilisation API

```python
import requests

# Test de génération
response = requests.post(
    "http://localhost:8190/generate",
    json={
        "prompt": "A beautiful sunset over mountains",
        "negative_prompt": "blurry, low quality",
        "width": 1024,
        "height": 1024,
        "num_inference_steps": 50,
        "guidance_scale": 7.5
    }
)

# Récupérer l'image
if response.status_code == 200:
    image_data = response.json()["image"]
    # Traiter l'image (base64 ou URL)
```

## 🧪 Commandes de Test

```powershell
# Vérifier que le service démarre
docker compose logs stable-diffusion-35

# Vérifier l'utilisation GPU
docker exec stable-diffusion-35 nvidia-smi

# Test health check
curl http://localhost:8190/health

# Tester la documentation Swagger
# Ouvrir: http://localhost:8190/docs

# Vérifier les modèles téléchargés
docker exec stable-diffusion-35 ls -lh /models/
docker exec stable-diffusion-35 du -sh /models/*
```

## 📊 Ressources Système

### Configuration Minimale
- **RAM**: 12 GB
- **GPU VRAM**: 10 GB (RTX 3080 minimum)
- **Espace Disque**: 15 GB (modèle + cache)

### Configuration Recommandée
- **RAM**: 24 GB
- **GPU VRAM**: 16 GB+ (RTX 3090 / 4090)
- **Espace Disque**: 30 GB

### Temps de Génération Estimés

| Résolution | RTX 3080 Ti | RTX 3090 |
|------------|-------------|----------|
| 512x512    | ~8s         | ~6s      |
| 1024x1024  | ~15s        | ~12s     |
| 1536x1536  | ~30s        | ~25s     |

## 🐛 Dépannage

### Le modèle ne se télécharge pas

```powershell
# Vérifier les logs
docker compose logs stable-diffusion-35 | Select-String -Pattern "download|error"

# Vérifier la connexion Hugging Face
docker exec stable-diffusion-35 curl -I https://huggingface.co
```

### Erreur "Token required"

Le modèle peut être gated. Solution:
1. Créer un token sur https://huggingface.co/settings/tokens
2. Ajouter `HUGGINGFACE_TOKEN` dans `.env.docker`
3. Redémarrer le service

### GPU non détecté

```powershell
# Vérifier NVIDIA Docker runtime
docker run --rm --gpus all nvidia/cuda:12.1.0-base-ubuntu22.04 nvidia-smi
```

### Mémoire GPU insuffisante

Solutions:
- Réduire la résolution (512x512 au lieu de 1024x1024)
- Activer `enable_attention_slicing` dans config.json
- Activer `enable_cpu_offload` (plus lent mais utilise moins de VRAM)
- Utiliser le GPU avec plus de VRAM (RTX 3090)

### Génération trop lente

Optimisations:
- Vérifier que `TORCH_COMPILE=1` est activé
- Réduire `num_inference_steps` (25-30 au lieu de 50)
- Utiliser `fp16` precision (déjà par défaut)

## 📚 Ressources

- [Stable Diffusion 3.5 Hugging Face](https://huggingface.co/stabilityai/stable-diffusion-3.5-large)
- [Diffusers Documentation](https://huggingface.co/docs/diffusers)
- [API FastAPI Docs](http://localhost:8190/docs) (une fois service démarré)
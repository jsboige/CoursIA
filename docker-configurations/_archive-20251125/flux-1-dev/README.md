# FLUX.1-dev Service - ComfyUI

## 📋 Description

Service de génération d'images basé sur le modèle FLUX.1-dev via ComfyUI.
Optimisé pour la création artistique haute qualité avec workflows personnalisables.

## 🎯 Rôle du Service

- Génération d'images créatives haute résolution
- Support de workflows ComfyUI avancés
- Interface web interactive sur port 8189
- API REST pour intégration programmatique

## 📁 Structure des Fichiers

```
flux-1-dev/
├── config/
│   └── extra_model_paths.yaml    # Configuration des chemins de modèles
├── models/                        # Modèles à placer ici (non inclus dans Git)
│   ├── checkpoints/              # Modèles FLUX principaux (.safetensors)
│   ├── vae/                      # VAE encoders
│   ├── clip/                     # CLIP text encoders
│   └── loras/                    # LoRA fine-tunings (optionnel)
├── custom_nodes/                  # Custom nodes ComfyUI (optionnel)
├── workflows/                     # Workflows ComfyUI (.json)
└── README.md                      # Ce fichier
```

## 📦 Modèles Requis

### Modèles Principaux (~24 GB total)

Les modèles doivent être téléchargés depuis Hugging Face et placés dans les répertoires appropriés :

1. **FLUX.1-dev checkpoint** (~23.8 GB)
   - Source: https://huggingface.co/black-forest-labs/FLUX.1-dev
   - Fichier: `flux1-dev.safetensors`
   - Destination: `models/checkpoints/`

2. **VAE (Autoencoder)** (~335 MB)
   - Source: https://huggingface.co/black-forest-labs/FLUX.1-dev
   - Fichier: `ae.safetensors`
   - Destination: `models/vae/`

3. **CLIP Text Encoder** (~246 MB)
   - Source: https://huggingface.co/comfyanonymous/flux_text_encoders
   - Fichier: `clip_l.safetensors`
   - Destination: `models/clip/`

⚠️ **IMPORTANT**: Les modèles sont volumineux (~24 GB). Prévoir temps de téléchargement.

## 🔧 Configuration

### Fichier `config/extra_model_paths.yaml`

Définit les chemins des modèles dans le container. Configuration par défaut:

```yaml
comfyui:
  base_path: /app/models
  checkpoints: /app/models/checkpoints
  vae: /app/models/vae
  clip: /app/models/clip
```

### Variables d'Environnement Docker

- `CUDA_VISIBLE_DEVICES=0` : GPU à utiliser (0 ou 1)
- `COMFYUI_ARGS` : Arguments de lancement ComfyUI

## 🚀 Utilisation

### Démarrage du Service

```powershell
# Via docker-compose principal
docker compose up flux-1-dev -d

# Via docker-compose de test
docker compose -f docker-compose.test.yml up comfyui-test -d
```

### Accès à l'Interface

- **Interface Web**: http://localhost:8189
- **API Health**: http://localhost:8189/system_stats

### Test de Génération

1. Ouvrir http://localhost:8189 dans un navigateur
2. Charger un workflow ou utiliser l'interface par défaut
3. Entrer un prompt texte
4. Cliquer sur "Queue Prompt"
5. Les images générées apparaissent dans l'interface

## 🧪 Commandes de Test

```powershell
# Vérifier que le service démarre
docker compose logs flux-1-dev

# Vérifier l'utilisation GPU
docker exec flux-1-dev nvidia-smi

# Vérifier les modèles chargés
docker exec flux-1-dev ls -lh /app/models/checkpoints
docker exec flux-1-dev ls -lh /app/models/vae
docker exec flux-1-dev ls -lh /app/models/clip

# Test API health
curl http://localhost:8189/system_stats
```

## 📊 Ressources Système

### Configuration Minimale
- **RAM**: 8 GB
- **GPU VRAM**: 8 GB (RTX 3060 minimum)
- **Espace Disque**: 30 GB (modèles + cache)

### Configuration Recommandée
- **RAM**: 16 GB
- **GPU VRAM**: 12 GB+ (RTX 3080 Ti / 3090)
- **Espace Disque**: 50 GB

## 🐛 Dépannage

### Le service ne démarre pas
```powershell
# Vérifier les logs
docker compose logs flux-1-dev

# Vérifier que les modèles sont présents
ls -R docker-configurations/flux-1-dev/models/
```

### GPU non détecté
```powershell
# Vérifier NVIDIA Docker runtime
docker run --rm --gpus all nvidia/cuda:11.8.0-base-ubuntu22.04 nvidia-smi
```

### Mémoire GPU insuffisante
- Réduire la résolution d'image dans le workflow
- Activer `--lowvram` dans COMFYUI_ARGS
- Utiliser le GPU avec plus de VRAM (RTX 3090)

## 📚 Ressources

- [ComfyUI GitHub](https://github.com/comfyanonymous/ComfyUI)
- [FLUX.1 Hugging Face](https://huggingface.co/black-forest-labs/FLUX.1-dev)
- [Documentation Workflows](../docs/genai/workflow-examples.md)
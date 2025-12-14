# ComfyUI + Qwen Image-Edit Docker Configuration

Configuration Docker pour ComfyUI avec le modèle Qwen-Image-Edit-2509-FP8 sur GPU RTX 3090.

## Architecture

```
GPU 0 (RTX 3080 Ti 16GB): Forge SD XL Turbo (Port 7860)
GPU 1 (RTX 3090 24GB):    ComfyUI + Qwen Image-Edit (Port 8188)
```

### Mapping GPU Critique

**IMPORTANT**: Le mapping GPU est inversé entre PyTorch et nvidia-smi:

```
nvidia-smi GPU 0 = PyTorch GPU 1 (RTX 3080 Ti - 16GB)
nvidia-smi GPU 1 = PyTorch GPU 0 (RTX 3090 - 24GB) ← Utilisé par ComfyUI
```

**Configuration validée**: `CUDA_VISIBLE_DEVICES=0` pour utiliser la RTX 3090

## Prérequis

### 1. Installation ComfyUI en WSL

ComfyUI doit être installé et configuré dans WSL Ubuntu:

```bash
# Workspace par défaut
/home/jesse/SD/workspace/comfyui-qwen/ComfyUI

# Structure requise:
ComfyUI/
├── venv/                              # Virtual environment Python
├── models/
│   └── checkpoints/
│       └── Qwen-Image-Edit-2509-FP8/  # Modèle Qwen (54GB)
├── custom_nodes/
│   └── ComfyUI-QwenImageWanBridge/    # Custom node Qwen
└── main.py                            # Point d'entrée ComfyUI

**Note**: Avec la nouvelle structure, les modèles sont maintenant partagés via `../shared/models/`
```

### 2. Modèle Qwen Image-Edit

- **Nom**: Qwen-Image-Edit-2509-FP8
- **Taille**: ~54GB (quantifié FP8)
- **Emplacement**: `models/checkpoints/Qwen-Image-Edit-2509-FP8/`

### 3. Modèle Z-Image Turbo (Lumina-Next)

- **Nom**: Z-Image-Turbo (Architecture Lumina-Next-SFT)
- **Format**: Safetensors (Diffusers native)
- **Taille**: ~2.5GB (Modèle principal) + ~2.5GB (Text Encoder)
- **Emplacement**:
  - UNet/Transformer : `models/diffusers/z_image_turbo/` (ou structure Diffusers standard)
  - Text Encoder : `models/clip/gemma-2-2b-it.safetensors` (Gemma 2 2B)
- **Architecture**: Utilise un wrapper Diffusers spécialisé pour ComfyUI.

### 4. Custom Nodes

#### A. Qwen Image-Edit (Principal)
- **Nom**: ComfyUI-QwenImageWanBridge
- **Repository**: https://github.com/gokayfem/ComfyUI-QwenImageWanBridge
- **Emplacement**: `custom_nodes/ComfyUI-QwenImageWanBridge/`

#### B. Z-Image Turbo (Nouveau - Phase 39)
- **Nom**: ComfyUI-Lumina-Next-SFT-DiffusersWrapper
- **Repository**: (Interne/Adapté) Wrapper autour de `diffusers`
- **Emplacement**: `custom_nodes/ComfyUI-Lumina-Next-SFT-DiffusersWrapper/`
- **Usage**: Support natif et optimisé de l'architecture Lumina-Next via la librairie Diffusers.

### 5. Docker avec GPU Support

```bash
# Vérifier support GPU Docker
docker run --rm --gpus all nvidia/cuda:12.4.0-base-ubuntu22.04 nvidia-smi
```

## Configuration

### 1. Copier .env.example vers .env

```bash
cp .env.example .env
```

### 2. Ajuster les variables dans .env

```bash
# GPU Configuration
GPU_DEVICE_ID=0                # PyTorch GPU 0 = RTX 3090
CUDA_VISIBLE_DEVICES=0
NVIDIA_VISIBLE_DEVICES=0

# Port ComfyUI
COMFYUI_PORT=8188

# Chemin workspace WSL (ancienne configuration)
# COMFYUI_WORKSPACE_PATH=\\wsl.localhost\Ubuntu\home\jesse\SD\workspace\comfyui-qwen\ComfyUI

# Nouvelle configuration avec volumes partagés
COMFYUI_WORKSPACE_PATH=./workspace

# Timezone
TZ=Europe/Paris
```

## Utilisation

### Démarrer le container

```bash
# Depuis le répertoire docker-configurations/services/comfyui-qwen/
docker-compose up -d
```

### Suivre les logs

```bash
docker-compose logs -f
```

### Logs au démarrage (normal)

```
=== ComfyUI + Qwen Image-Edit Container ===
Installing system dependencies...
Checking workspace...
Activating virtual environment...
Verifying PyTorch and CUDA...
PyTorch: 2.6.0+cu124
CUDA: True
GPU: NVIDIA GeForce RTX 3090
Verifying Qwen model...
Qwen model found: models/checkpoints/Qwen-Image-Edit-2509-FP8
Verifying custom node...
Qwen custom node found: custom_nodes/ComfyUI-QwenImageWanBridge
=== Starting ComfyUI on port 8188 ===
GPU: RTX 3090 (CUDA_VISIBLE_DEVICES=0)
URL: http://localhost:8188
======================================
Total VRAM 24576 MB, total RAM 31943 MB
To see the GUI go to: http://0.0.0.0:8188
```

### Accéder à ComfyUI

```bash
# Navigateur
http://localhost:8188

# Ou depuis PowerShell
Start-Process "http://localhost:8188"
```

### Arrêter le container

```bash
docker-compose down
```

### Redémarrer le container

```bash
docker-compose restart
```

## Monitoring

### Vérifier le statut

```bash
docker-compose ps
```

### Vérifier l'utilisation GPU

```bash
# Depuis Windows
nvidia-smi

# Depuis le container
docker exec comfyui-qwen nvidia-smi
```

### Health Check

Le container expose un endpoint de health check:

```bash
curl http://localhost:8188/system_stats
```

## Dépannage

### Le container ne démarre pas

1. **Vérifier que venv existe dans WSL**:
```bash
wsl ls -la /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/venv
```

2. **Vérifier que le modèle Qwen est présent**:
```bash
wsl ls -la /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/checkpoints/
```

3. **Vérifier les logs Docker**:
```bash
docker-compose logs
```

### GPU non détectée

1. **Vérifier le mapping GPU**:
```bash
docker exec comfyui-qwen nvidia-smi
```

2. **Vérifier PyTorch**:
```bash
docker exec comfyui-qwen bash -c "source venv/bin/activate && python3 -c 'import torch; print(torch.cuda.is_available(), torch.cuda.get_device_name(0))'"
```

### Port 8188 déjà utilisé

Changer le port dans `.env`:
```bash
COMFYUI_PORT=8189  # Ou autre port disponible
```

Puis redémarrer:
```bash
docker-compose down && docker-compose up -d
```

### Modifier la configuration

Après modification du `.env`:
```bash
docker-compose down
docker-compose up -d
```

## Performance

### Métriques typiques

- **Temps démarrage**: ~10-15 secondes
- **VRAM idle**: ~1GB / 24GB (4%)
- **VRAM avec modèle chargé**: ~8-12GB / 24GB
- **RAM utilisée**: ~4-6GB

### Optimisations

Le container est configuré avec:
- `--use-split-cross-attention`: Réduit l'utilisation VRAM
- `--preview-method auto`: Optimise les previews
- Lazy loading: Modèles chargés à la demande

## Intégration Reverse Proxy

Pour exposer ComfyUI via IIS avec HTTPS:

1. **Créer site IIS** `qwen-image-edit.myia.io`
2. **Configurer reverse proxy** vers `http://localhost:8188`
3. **Ajouter certificat SSL** `*.myia.io`

Voir documentation Phase 11 pour détails.

## Workflows Qwen Image-Edit

### Fonctionnalités supportées

- **Image Generation**: Génération d'images depuis texte
- **Image-to-Image**: Transformation d'images existantes
- **Multi-image Editing**: Édition de 1-3 images simultanément
- **Pose Transfer**: Transfert de pose entre images
- **Style Transfer**: Application de styles

### Exemples de workflows

Voir `../../archive/2025-11-26/comfyui-workflows/` pour exemples de workflows Qwen.

## Maintenance

### Backup Configuration

```bash
# Backup du workspace (sans modèles)
wsl tar -czf comfyui-backup.tar.gz \
  --exclude='models/checkpoints' \
  --exclude='venv' \
  /home/jesse/SD/workspace/comfyui-qwen/ComfyUI
```

### Mise à jour ComfyUI

```bash
# Dans WSL
cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI
git pull
source venv/bin/activate
pip install -r requirements.txt

# Redémarrer container
docker-compose restart
```

### Mise à jour Custom Node

```bash
# Dans WSL
cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/custom_nodes/ComfyUI-QwenImageWanBridge
git pull

# Redémarrer container
docker-compose restart
```

## Architecture Technique

### Stack

- **Base Image**: nvidia/cuda:12.4.0-devel-ubuntu22.04
- **Python**: 3.12.3
- **PyTorch**: 2.6.0+cu124
- **CUDA**: 12.4
- **ComfyUI**: 0.3.664+

### Volumes

- **Type**: Bind mount (accès direct au workspace WSL)
- **Source**: WSL Ubuntu filesystem
- **Target**: `/workspace/ComfyUI` dans container
- **Avantages**: 
  - Modifications directes dans WSL
  - Pas de duplication de données
  - Partage workspace entre standalone et Docker

### Network

- **Type**: Bridge network
- **Nom**: comfyui-network
- **Isolation**: Container isolé des autres services
- **Port Mapping**: 8188:8188 (host:container)

## Références

### Documentation

- [Checkpoint Sémantique 1](../../docs/genai-suivis/2025-10-13_11_checkpoint-semantique-1-comfyui-base.md)
- [Checkpoint Sémantique 2](../../docs/genai-suivis/2025-10-13_11_checkpoint-semantique-2-standalone-validation.md)
- [ComfyUI Official](https://github.com/comfyanonymous/ComfyUI)
- [Qwen Image-Edit](https://huggingface.co/Qwen/Qwen-Image-Edit-2509)

### Scripts Utiles

- `resolve-gpu-mapping.sh`: Test mapping GPU
- `launch-comfyui-standalone.sh`: Lancement standalone
- `test-comfyui-background.sh`: Test background avec validation

## Support

Pour questions ou problèmes:
1. Consulter les logs: `docker-compose logs`
2. Vérifier GPU: `docker exec comfyui-qwen nvidia-smi`
3. Tester standalone dans WSL pour isoler problème
4. Consulter checkpoints sémantiques pour configuration validée

---

**Dernière mise à jour**: 2025-11-26
**Version**: 2.0.0 (Migration vers volumes partagés)
**Statut**: Production Ready ✅

## Migration vers les volumes partagés

Ce service a été migré vers la nouvelle structure avec volumes partagés :
- Les modèles sont maintenant dans `../shared/models/`
- Le cache utilise `../shared/cache/`
- Les sorties sont dirigées vers `../shared/outputs/`

Cette migration permet :
- Partage des modèles entre plusieurs services
- Optimisation de l'espace disque
- Gestion centralisée des ressources
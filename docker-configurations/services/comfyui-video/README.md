# ComfyUI Video - Video Generation

Configuration Docker pour ComfyUI avec support video (HunyuanVideo, Wan 2.1/2.2, AnimateDiff) sur GPU RTX 3090.

## Overview

| Parametre | Valeur |
|-----------|--------|
| Modeles | HunyuanVideo, Wan 2.1/2.2, AnimateDiff |
| Port | 8189 |
| GPU | RTX 3090 (PyTorch GPU 0 = nvidia-smi GPU 1) |
| VRAM | ~9GB+ (selon modele charge) |
| URL cloud | https://comfyui-video.myia.io |

## Demarrage

```bash
# Depuis docker-configurations/services/comfyui-video/
docker-compose up -d

# Suivre les logs
docker-compose logs -f

# Arreter
docker-compose down
```

## Custom Nodes

| Node | Repository | Description |
|------|-----------|-------------|
| ComfyUI-AnimateDiff-Evolved | Kosinkadink/ComfyUI-AnimateDiff-Evolved | Animation et generation video |
| ComfyUI-VideoHelperSuite | Kosinkadink/ComfyUI-VideoHelperSuite | Utilitaires video (load, save, combine) |
| ComfyUI-HunyuanVideoWrapper | kijai/ComfyUI-HunyuanVideoWrapper | Tencent HunyuanVideo |
| ComfyUI-GGUF | city96/ComfyUI-GGUF | Support modeles GGUF quantizes |

## Configuration (.env)

Copier `.env.example` vers `.env` et adapter les valeurs :

```bash
cp .env.example .env
```

| Variable | Defaut | Description |
|----------|--------|-------------|
| `GPU_DEVICE_ID` | `0` | GPU PyTorch (0 = RTX 3090) |
| `COMFYUI_VIDEO_PORT` | `8189` | Port externe |
| `COMFYUI_WORKSPACE_PATH` | `./workspace` | Chemin workspace ComfyUI |
| `CIVITAI_TOKEN` | - | Token CivitAI pour telechargement modeles |
| `HF_TOKEN` | - | Token Hugging Face |
| `COMFYUI_LOGIN_ENABLED` | `true` | Activer authentification |
| `COMFYUI_USERNAME` | - | Utilisateur |
| `COMFYUI_PASSWORD` | - | Mot de passe |
| `COMFYUI_VIDEO_TOKEN` | - | Bearer token API |
| `API_TIMEOUT` | `600` | Timeout requetes API (secondes) |

### Mapping GPU

**IMPORTANT** : Le mapping GPU est inverse entre PyTorch et nvidia-smi :

```
nvidia-smi GPU 0 = PyTorch GPU 1 (RTX 3080 Ti - 16GB)
nvidia-smi GPU 1 = PyTorch GPU 0 (RTX 3090 - 24GB)  <-- ComfyUI Video
```

`GPU_DEVICE_ID=0` correspond a la RTX 3090.

**EXCLUSIF avec comfyui-qwen** : Les deux services partagent le meme GPU. Ne pas les lancer simultanement.

## Architecture

- **Base** : ComfyUI compile depuis les sources, Python 3.11, PyTorch CUDA 12.1
- **Quantization** : Support INT8/FP8 via Optimum Quanto + bitsandbytes
- **GGUF** : Support modeles GGUF quantizes via ComfyUI-GGUF
- **Idle Monitor** : Sidecar qui decharge les modeles apres inactivite (`IDLE_TIMEOUT=1200s`)
- **Auth** : ComfyUI-Login avec bcrypt

## Fichiers

| Fichier | Description |
|---------|-------------|
| `docker-compose.yml` | Service principal + sidecar idle-monitor |
| `entrypoint.sh` | Installation auto + lancement ComfyUI |
| `install_video_nodes.sh` | Installation manuelle des custom nodes |
| `.env.example` | Template de configuration |

## Volumes

Le workspace ComfyUI est separe de comfyui-qwen pour eviter les conflits de custom nodes et de configuration :

| Source hote | Cible container | Description |
|-------------|-----------------|-------------|
| `COMFYUI_WORKSPACE_PATH` | `/workspace/ComfyUI` | Code + venv + custom nodes |
| `../../shared/models` | `/workspace/ComfyUI/models` | Modeles partages |
| `../../shared/cache` | `/workspace/ComfyUI/cache` | Cache Hugging Face |
| `../../shared/outputs` | `/workspace/ComfyUI/output` | Sorties generees |

# Profils de Deploiement GenAI

Ce repertoire definit les profils de deploiement pour la stack GenAI.

## Contrainte Materielle

La machine dispose de deux GPUs avec des contraintes memoire:

| GPU Index (nvidia-smi) | Modele | VRAM | PyTorch ID | Usage Recommande |
|-------------------------|--------|------|------------|------------------|
| 0 | RTX 3080 Ti Laptop | 16 GB | 1 | Forge SD XL Turbo |
| 1 | RTX 3090 | 24 GB | 0 | ComfyUI Qwen/Video, Whisper |

**ATTENTION**: Le mapping PyTorch est inverse par rapport a nvidia-smi:
- `CUDA_VISIBLE_DEVICES=0` dans ComfyUI utilise la RTX 3090 (nvidia-smi GPU 1)
- `--gpu-device-id 1` dans Forge utilise la RTX 3080 Ti (nvidia-smi GPU 0)

## Services Disponibles

| Service | Port | GPU | VRAM | Description |
|---------|------|-----|------|-------------|
| comfyui-qwen | 8188 | RTX 3090 | 20GB+ | Edition d'images Qwen-Image-Edit |
| forge-turbo | 17861 | RTX 3080 Ti | 8GB+ | Generation SDXL Turbo |
| vllm-zimage | 8001 | RTX 3080 Ti | 15GB+ | Text-to-image Lumina/Z-Image |
| whisper-webui | 36540 | RTX 3090 | 10GB+ | Transcription Whisper (Gradio) |
| comfyui-video | 8189 | RTX 3090 | 20GB+ | Generation video (AnimateDiff) |

## Profils GPU

Gestion via CLI: `python scripts/genai-stack/genai.py gpu profile <action>`

### 1. `image_default` - Services Image (par defaut)

**Demarrer**: comfyui-qwen, forge-turbo
**Arreter**: comfyui-video
**GPU 0 (RTX 3090)**: comfyui-qwen (20GB)
**GPU 1 (RTX 3080 Ti)**: forge-turbo (6GB)

```bash
python scripts/genai-stack/genai.py gpu profile apply image_default
```

### 2. `audio_api` - Audio API-only

Aucun changement de services. Notebooks utilisant uniquement les APIs cloud (OpenAI TTS/STT).

```bash
python scripts/genai-stack/genai.py gpu profile apply audio_api
```

### 3. `audio_local_gpu` - Audio modeles locaux

**Arreter**: comfyui-qwen, whisper-webui, vllm-zimage, comfyui-video
**GPU 0 (RTX 3090)**: Kernel notebook (jusqu'a 24GB)
**GPU 1 (RTX 3080 Ti)**: forge-turbo (6GB, reste actif)

```bash
python scripts/genai-stack/genai.py gpu profile apply audio_local_gpu
```

Utilise pour: Whisper local, Chatterbox TTS, XTTS, MusicGen, Demucs.

### 4. `video_comfyui` - Video via ComfyUI

**Demarrer**: comfyui-video
**Arreter**: comfyui-qwen, whisper-webui, vllm-zimage
**GPU 0 (RTX 3090)**: comfyui-video (20GB)

```bash
python scripts/genai-stack/genai.py gpu profile apply video_comfyui
```

Utilise pour: AnimateDiff, HunyuanVideo via nodes ComfyUI.

### 5. `video_local_heavy` - Video gros modeles

**Arreter**: TOUS les services (comfyui-qwen, whisper-webui, vllm-zimage, comfyui-video, forge-turbo)
**GPU 0 (RTX 3090)**: Kernel notebook (18-24GB)
**GPU 1 (RTX 3080 Ti)**: Libre

```bash
python scripts/genai-stack/genai.py gpu profile apply video_local_heavy
```

Utilise pour: HunyuanVideo (18GB), Qwen-VL (18GB), orchestration video.

### 6. `video_local_light` - Video modeles legers

**Arreter**: comfyui-qwen, vllm-zimage, comfyui-video
**GPU 0 (RTX 3090)**: Libre ou kernel
**GPU 1 (RTX 3080 Ti)**: Kernel notebook (8-10GB)

```bash
python scripts/genai-stack/genai.py gpu profile apply video_local_light
```

Utilise pour: LTX-Video (8GB), Wan 2.1 (10GB), SVD (10GB), ESRGAN (4GB).

## Batches d'Execution

Execution sequentielle des 32 notebooks Audio/Video organisee en 8 batches:

| Batch | Profil GPU | Notebooks | Description |
|-------|-----------|-----------|-------------|
| 1 | audio_api | 7 | API-only + local sans GPU |
| 2 | video_local_light | 3 | Audio/Video GPU leger (2-6GB) |
| 3 | audio_local_gpu | 2 | Audio GPU moyen (8-10GB) |
| 4 | audio_local_gpu | 6 | Audio orchestration/apps |
| 5 | video_local_light | 3 | Video GPU leger/moyen (8-12GB) |
| 6 | video_local_heavy | 3 | Video GPU lourd (18-24GB) |
| 7 | video_comfyui | 1 | Video ComfyUI nodes |
| 8 | video_local_heavy | 7 | Video orchestration/apps |

```bash
# Executer un batch specifique
python scripts/genai-stack/genai.py notebooks --batch 1

# Executer un groupe
python scripts/genai-stack/genai.py notebooks --group audio_api

# Executer une serie complete
python scripts/genai-stack/genai.py notebooks --series audio
```

## Estimation VRAM par Modele

### Image

| Modele | VRAM Min | GPU Cible |
|--------|----------|-----------|
| Qwen-Image-Edit-2509-FP8 | 12 GB | RTX 3090 |
| Z-Image Turbo (Lumina-Next) | 6 GB | RTX 3080 Ti |
| SDXL Turbo | 6 GB | RTX 3080 Ti |

### Audio

| Modele | VRAM Min | GPU Cible |
|--------|----------|-----------|
| Whisper large-v3-turbo | 10 GB | RTX 3090 |
| Chatterbox TTS | 8 GB | RTX 3090 |
| XTTS v2 | 6 GB | RTX 3080 Ti |
| MusicGen medium | 10 GB | RTX 3090 |
| Demucs v4 | 4 GB | RTX 3080 Ti |
| Kokoro TTS | 2 GB | RTX 3080 Ti |

### Video

| Modele | VRAM Min | GPU Cible |
|--------|----------|-----------|
| HunyuanVideo (INT8) | 18 GB | RTX 3090 |
| Qwen2.5-VL (video) | 18 GB | RTX 3090 |
| AnimateDiff | 12 GB | RTX 3090 |
| SVD (Stable Video Diffusion) | 10 GB | RTX 3090 |
| Wan 2.1/2.2 (INT8) | 10 GB | RTX 3090 |
| LTX-Video | 8 GB | RTX 3080 Ti |
| Real-ESRGAN/RIFE | 4 GB | RTX 3080 Ti |

## Commandes Utiles

```bash
# Status complet des services
python scripts/genai-stack/genai.py docker status

# Lister les profils GPU
python scripts/genai-stack/genai.py gpu profile list

# Detecter le profil actuel
python scripts/genai-stack/genai.py gpu profile current

# Verifier la VRAM disponible
python scripts/genai-stack/genai.py gpu

# Verifier si un modele tient (ex: 18000 MiB)
python scripts/genai-stack/genai.py gpu check-fit 18000 --gpu 1

# Appliquer automatiquement le profil pour un groupe
python scripts/genai-stack/genai.py gpu schedule video_diffusion_heavy

# Validation syntaxe notebooks Audio
python scripts/genai-stack/genai.py validate --notebooks --series audio

# Validation syntaxe notebooks Video
python scripts/genai-stack/genai.py validate --notebooks --series video
```

## Bonnes Pratiques

1. **Toujours verifier la VRAM** avant d'appliquer un profil
2. **Utiliser les profils GPU** pour gerer les services automatiquement
3. **Executer par batch** pour les notebooks Audio/Video
4. **Monitorer avec nvidia-smi** pendant l'utilisation intensive
5. **Whisper-WebUI coexiste** avec ComfyUI Qwen sur RTX 3090 en usage normal

---

**Derniere mise a jour**: 2026-02-13
**Version**: 2.0.0

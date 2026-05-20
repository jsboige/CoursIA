# Docker Configurations - GenAI Services

Configurations Docker pour les 11 services GenAI sur po-2023.

## Vue d'ensemble

| Categorie | Services | Total |
|-----------|----------|-------|
| Image | Qwen Image Edit, Z-Image, SD Forge Turbo, SD Forge, SD.Next | 5 |
| Audio | Whisper STT, Kokoro TTS, MusicGen, Demucs, Qwen ASR | 5 |
| Video | ComfyUI Video | 1 |

## Services

### Image

| Service | Modele | VRAM | Port | Cloud URL | Docker |
|---------|--------|------|------|-----------|--------|
| [comfyui-qwen](services/comfyui-qwen/) | qwen_image_edit_2509 | ~16GB | 8188 | https://qwen-image-edit.myia.io | comfyui-qwen |
| [vllm-zimage](services/vllm-zimage/) | Lumina-Next-SFT | ~9GB | 8001 | https://z-image.myia.io | vllm-zimage |
| [forge-turbo](services/forge-turbo/) | SDXL Turbo | ~2GB | 17861 | https://turbo.stable-diffusion-webui-forge.myia.io | forge-turbo |
| [sd-forge-main](services/sd-forge-main/) | SDXL 1.0 | ~2GB | 7860 | https://stable-diffusion-webui-forge.myia.io | sd-forge-main |
| [sdnext](services/sdnext/) | SDXL/SD1.5 | ~3GB | 7861 | https://sdnext.myia.io | sdnext |

### Audio

| Service | Modele | VRAM | Port | Cloud URL | Docker |
|---------|--------|------|------|-----------|--------|
| [whisper-api](services/whisper-api/) | faster-whisper large-v3-turbo | ~10GB | 8190 | https://whisper-api.myia.io | whisper-api |
| [tts-api](services/tts-api/) | kokoro-v0_19 | ~2GB | 8191 | https://tts-api.myia.io | tts-api |
| [musicgen-api](services/musicgen-api/) | facebook/musicgen-medium | ~10GB | 8192 | https://musicgen-api.myia.io | musicgen-api |
| [demucs-api](services/demucs-api/) | htdemucs_ft | ~4GB | 8193 | https://demucs-api.myia.io | demucs-api |
| [qwen-asr-api](services/qwen-asr-api/) | Qwen3-ASR-1.7B | ~4GB | 8195 | https://stt.myia.io/qwen | qwen-asr-api |

### Video

| Service | Modele | VRAM | Port | Cloud URL | Docker |
|---------|--------|------|------|-----------|--------|
| [comfyui-video](services/comfyui-video/) | HunyuanVideo, Wan, AnimateDiff | ~9GB | 8189 | https://comfyui-video.myia.io | comfyui-video |

## Allocation GPU

| GPU | Modele | VRAM | Services |
|-----|--------|------|----------|
| 0 (nvidia-smi) | RTX 3080 Ti | 16GB | Qwen Image Edit |
| 1 (nvidia-smi) | RTX 3090 | 24GB | Tous les autres services |

Note: Le mapping PyTorch peut etre inverse par rapport a nvidia-smi selon la config CUDA.

## Gestion des services

```bash
# Statut
python scripts/genai-stack/genai.py docker status

# Demarrer / arreter
python scripts/genai-stack/genai.py docker start all
python scripts/genai-stack/genai.py docker stop all

# Tester les endpoints
python scripts/genai-stack/genai.py docker test --remote

# Authentification
python scripts/genai-stack/genai.py auth audit
python scripts/genai-stack/genai.py auth sync
```

## Authentification

Tous les services utilisent l'authentification Bearer Token via le reverse proxy IIS :
- Header: `Authorization: Bearer <token>`
- Tokens dans les fichiers `.env` de chaque service

## Architecture commune (services Audio)

Les 5 services audio partagent une architecture identique :

- **Lazy loading** : modele charge a la premiere requete, decharge apres 300s d'inactivite
- **Shared modules** : `services/shared/` monte en lecture seule (`lazy_model.py`, `auth_middleware.py`)
- **FFmpeg** : conversion automatique des formats audio
- **CUDA fallback** : bascule sur CPU si CUDA indisponible
- **API OpenAI-compatible** : endpoints `/v1/audio/transcriptions`, `/v1/audio/speech`, etc.

### Configuration hybride

Les services audio disposent de configurations hybrides (image ghcr.io + config locale) :

```bash
# Utiliser la config hybride
cd docker-configurations/services/whisper-api
docker-compose -f docker-compose-hybrid.yml up -d
```

## Structure

```
docker-configurations/
├── README.md
├── services/                   Configurations Docker des services
│   ├── shared/                 Modules partages (lazy_model.py, auth_middleware.py)
│   ├── comfyui-qwen/           Image - Qwen Image Edit [8188]
│   ├── vllm-zimage/            Image - Z-Image/Lumina [8001]
│   ├── forge-turbo/            Image - SD Forge Turbo [17861]
│   ├── sd-forge-main/          Image - SD Forge principal [7860]
│   ├── sdnext/                 Image - SD.Next [7861]
│   ├── whisper-api/            Audio - Whisper STT [8190]
│   ├── tts-api/                Audio - Kokoro TTS [8191]
│   ├── musicgen-api/           Audio - MusicGen [8192]
│   ├── demucs-api/             Audio - Demucs [8193]
│   ├── qwen-asr-api/           Audio - Qwen ASR [8195]
│   └── comfyui-video/          Video - ComfyUI Video [8189]
├── profiles/                   Profils de deploiement GPU
├── cache/                      Cache HuggingFace, CivitAI
├── models/                     Modeles partages
├── .secrets/                   Tokens (gitignore)
└── _archive-20251125/         Configurations obsoletes
```

## Prerequis

- Docker Desktop avec support WSL2 et NVIDIA Container Toolkit
- GPU: RTX 3090 (24GB) + RTX 3080 Ti (16GB)
- RAM: 32GB+
- Stockage: 100GB+ pour les modeles

---

Derniere mise a jour: 2026-04-26

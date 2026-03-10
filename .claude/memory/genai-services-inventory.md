# GenAI Services Inventory - po-2023

**Responsabilités** :
- **myia-ai-01** : LLMs (zwz/mini, qwen 3.5/medium) + Qdrant
- **po-2026** : Embeddings
- **po-2023 (MOI)** : TOUS les services GenAI ci-dessous

---

## Services IMAGE (5)

| Service | Modèle | VRAM | URL Cloud | Port Local | Docker | Status |
|---------|--------|------|-----------|------------|--------|--------|
| **Qwen Image Edit** | qwen_image_edit_2509 | ~16GB | https://qwen-image-edit.myia.io | 8188 | ✅ comfyui-qwen | ✅ UP |
| **Z-Image/Lumina** | Lumina-Next-SFT | ~9GB | https://z-image.myia.io | 8001 | ✅ vllm-zimage | ✅ UP |
| **SD Forge Turbo** | SDXL Turbo | ~2GB | https://turbo.stable-diffusion-webui-forge.myia.io | 17861 | ✅ forge-turbo | ✅ UP |
| **SD Forge (full)** | SDXL 1.0 | ~2GB | https://stable-diffusion-webui-forge.myia.io | 7860 | ✅ sd-forge-main | ✅ UP |
| **SD.Next** | SDXL/SD1.5 | ~3GB | https://sdnext.myia.io | 7861 | ✅ sdnext | ✅ UP |

**Docker existants** : `docker-configurations/services/`
- `comfyui-qwen/` - ✅ UP
- `vllm-zimage/` - ✅ UP
- `forge-turbo/` - ✅ UP
- `sd-forge-main/` - ✅ UP
- `sdnext/` - ✅ UP

---

## Services AUDIO (4)

| Service | Modèle | VRAM | URL Cloud | Port Local | Docker | Status |
|---------|--------|------|-----------|------------|--------|--------|
| **Whisper STT** | faster-whisper large-v3 | ~10GB | https://whisper-api.myia.io | 8190/36540 | ✅ whisper-api | ✅ UP |
| **Kokoro TTS** | kokoro-v0_19 | ~2GB | https://tts-api.myia.io | 8191 | ✅ tts-api | ✅ UP |
| **MusicGen** | facebook/musicgen-medium | ~10GB | https://musicgen-api.myia.io | 8192 | ✅ musicgen-api | ✅ UP |
| **Demucs** | htdemucs_ft | ~4GB | https://demucs-api.myia.io | 8193 | ✅ demucs-api | ✅ UP |

**Docker existants** : `docker-configurations/services/`

- `whisper-api/` - ✅ UP (API depuis main, avec lazy loading)
- `tts-api/` - ✅ UP (API depuis main, avec lazy loading)
- `musicgen-api/` - ✅ UP (API depuis main, avec lazy loading)
- `demucs-api/` - ✅ UP (API depuis main, avec lazy loading)
- `whisper-webui/` - ✅ UP (WebUI alternative)

**Configurations hybrides disponibles** :

- `whisper-api/docker-compose-hybrid.yml` - Image ghcr.io + config complète
- `tts-api/docker-compose-hybrid.yml` - Image ghcr.io + config complète
- `musicgen-api/docker-compose-hybrid.yml` - Image ghcr.io + config complète
- `demucs-api/docker-compose-hybrid.yml` - Image ghcr.io + config complète

---

## Services VIDEO (1)

| Service | Modèle | VRAM | URL Cloud | Port Local | Docker | Status |
|---------|--------|------|-----------|------------|--------|--------|
| **ComfyUI Video** | HunyuanVideo, Wan, AnimateDiff | ~9GB | https://comfyui-video.myia.io | 8189 | ✅ comfyui-video | ✅ UP |

**Existant** :
- `comfyui-video/` - Container UP et healthy

---

## Authentification

**Tous les services utilisent l'authentification IIS Bearer Token** :
- Header: `Authorization: Bearer <token>`
- Token dans `.env` : `COMFYUI_API_TOKEN`, `WHISPER_API_KEY`, `TTS_API_KEY`, etc.

**Gestion des tokens** :
```bash
python scripts/genai-stack/genai.py auth audit
python scripts/genai-stack/genai.py auth sync
```

---

## État GPU (po-2023)

| GPU | VRAM | Utilisation | Services |
|-----|------|-------------|----------|
| **0** (3080 Ti) | 16384 MB | 98% - 16065 MB | Qwen Image Edit (16GB) |
| **1** (3090) | 24576 MB | 53% - 12966 MB | ComfyUI Video (13GB), Z-Image, Forge Turbo, SD Forge, SD.Next, Audio services |

**Note** : GPU 0 reste saturé par Qwen Image Edit. Tous les autres services utilisent GPU 1. ComfyUI Video utilise maintenant GPU 1 correctement.

---

## Actions requises

### ✅ Services créés et démarrés

**Image** :
- [x] SD Forge principal (port 7860) - ✅ UP
- [x] SD.Next (port 7861) - ✅ UP

**Audio** :
- [x] API Whisper (port 8190) - ✅ UP
- [x] Kokoro TTS (port 8191) - ✅ UP
- [x] MusicGen (port 8192) - ✅ UP
- [x] Demucs (port 8193) - ✅ UP

**Video** :
- [x] ComfyUI Video (port 8189) - ✅ UP

### Future optimisation GPU
- Déplacer Qwen Image Edit vers GPU 1 (plus de VRAM dispo)
- OU utiliser quantization pour réduire VRAM

---

## Docker Compose Template

```yaml
services:
  service-name:
    image: ...
    ports:
      - "819X:819X"
    environment:
      - API_KEY=${SERVICE_API_KEY}
    deploy:
      resources:
        reservations:
          devices:
            - driver: nvidia
              device_ids: ['1']  # GPU 1 seulement
              capabilities: [gpu]
```

---

## Mise à jour : 2026-03-09

**Services opérationnels** : 10/10 ✅
- Image: 5/5 UP (Qwen Edit, Z-Image, Forge Turbo, SD Forge, SD.Next)
- Audio: 4/4 UP (Whisper, Kokoro TTS, MusicGen, Demucs)
- Video: 1/1 UP (ComfyUI Video)

**Tous les services GenAI sur po-2023 sont opérationnels.**

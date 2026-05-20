# GenAI Services - ComfyUI Image Generation

## Services disponibles

| Service | Modele | VRAM | Description |
|---------|--------|------|-------------|
| **Qwen Image Edit** | qwen_image_edit_2509 | ~29GB | Edition d'images avec prompts multimodaux |
| **Z-Image/Lumina** | Lumina-Next-SFT | ~10GB | Generation text-to-image haute qualite |

## Architecture Qwen (Phase 29)

Workflow ComfyUI pour Qwen Image Edit 2509 :

```
VAELoader (qwen_image_vae.safetensors, 16 channels)
    |
CLIPLoader (qwen_2.5_vl_7b_fp8_scaled.safetensors, type: sd3)
    |
UNETLoader (qwen_image_edit_2509_fp8_e4m3fn.safetensors)
    |
ModelSamplingAuraFlow (shift=3.0)
    |
CFGNorm (strength=1.0)
    |
TextEncodeQwenImageEdit (clip, prompt, vae)
    |
ConditioningZeroOut (negative)
    |
EmptySD3LatentImage (16 channels)
    |
KSampler (scheduler=beta, cfg=1.0, sampler=euler)
    |
VAEDecode
```

**Points critiques** :
- VAE 16 canaux (pas SDXL standard)
- `scheduler=beta` obligatoire
- `cfg=1.0` (pas de CFG classique, utilise CFGNorm)
- `ModelSamplingAuraFlow` avec shift=3.0

## Architecture Z-Image/Lumina

Workflow ComfyUI simplifie avec LuminaDiffusersNode :

```
LuminaDiffusersNode (Alpha-VLLM/Lumina-Next-SFT-diffusers)
    |
VAELoader (sdxl_vae.safetensors)
    |
VAEDecode
    |
SaveImage
```

**Parametres LuminaDiffusersNode** :
- `model_path`: "Alpha-VLLM/Lumina-Next-SFT-diffusers"
- `num_inference_steps`: 20-40
- `guidance_scale`: 3.0-5.0
- `scaling_watershed`: 0.3
- `proportional_attn`: true
- `max_sequence_length`: 256

**Note technique (Janvier 2025)** : Le node utilise `LuminaPipeline` (diffusers 0.34+), ancien nom `LuminaText2ImgPipeline` obsolete.

## Approches abandonnees

| Approche | Raison abandon |
|----------|----------------|
| Z-Image GGUF | Incompatibilite dimensionnelle (2560 vs 2304) entre RecurrentGemma et Gemma-2 |
| Qwen GGUF | Non teste, prefer les poids fp8 pour qualite |

## Scripts de gestion (`scripts/genai-stack/`)

**IMPORTANT pour agents** : Utiliser le CLI unifie `genai.py` au lieu de demarrer des kernels MCP directement.

```bash
# CLI unifie - aide
python scripts/genai-stack/genai.py --help

# Gestion services Docker
python scripts/genai-stack/genai.py docker status          # Statut services
python scripts/genai-stack/genai.py docker start all       # Demarrer tous les services
python scripts/genai-stack/genai.py docker test --remote   # Tester endpoints (local + remote)

# Validation stack ComfyUI
python scripts/genai-stack/genai.py validate --full        # Validation complete
python scripts/genai-stack/genai.py validate --nunchaku    # Test Nunchaku INT4 Lightning

# Validation notebooks
python scripts/genai-stack/genai.py validate --notebooks   # Syntaxe notebooks GenAI
python scripts/genai-stack/genai.py notebooks              # Execution Papermill

# GPU et modeles
python scripts/genai-stack/genai.py gpu                    # Verification VRAM
python scripts/genai-stack/genai.py models list-nodes      # Custom nodes ComfyUI
python scripts/genai-stack/genai.py models list-checkpoints # Checkpoints disponibles

# Authentification
python scripts/genai-stack/genai.py auth audit             # Audit securite tokens
python scripts/genai-stack/genai.py auth sync              # Synchroniser tokens
```

## Mapping notebooks GenAI Image -> services

| Notebooks | Service | Prerequis |
|-----------|---------|-----------|
| 01-1, 01-3 | OpenAI API (cloud) | OPENAI_API_KEY |
| 01-4, 02-3 | SD Forge | Service local ou myia.io |
| 01-5, 02-1 | ComfyUI Qwen | COMFYUI_AUTH_TOKEN, ~29GB VRAM |
| 02-4 | Z-Image/vLLM | ~10GB VRAM |
| 03-* | Multi-modeles | Tous les services |
| 04-* | Applications | Variable |

## Mapping notebooks Audio -> services

| Notebooks | Service | Prerequis |
|-----------|---------|-----------|
| Audio/01-1, 01-2 | OpenAI API (TTS/STT) | OPENAI_API_KEY |
| Audio/01-3 | Local (librosa, pydub) | Aucun |
| Audio/01-4 | Whisper local | GPU ~10 GB |
| Audio/01-5 | Kokoro TTS | GPU ~2 GB |
| Audio/02-1 | Chatterbox TTS | GPU ~8 GB |
| Audio/02-2 | XTTS v2 | GPU ~6 GB |
| Audio/02-3 | MusicGen | GPU ~10 GB |
| Audio/02-4 | Demucs v4 | GPU ~4 GB |
| Audio/03-* | Multi-modeles | Mixed |
| Audio/04-* | Applications | Mixed |

## Mapping notebooks Video -> services

| Notebooks | Service | Prerequis |
|-----------|---------|-----------|
| Video/01-1 | Local (moviepy, FFmpeg) | FFmpeg installe |
| Video/01-2 | OpenAI GPT-5 | OPENAI_API_KEY |
| Video/01-3 | Qwen2.5-VL local | GPU ~18 GB |
| Video/01-4 | Real-ESRGAN/RIFE | GPU ~4 GB |
| Video/01-5 | AnimateDiff | GPU ~12 GB |
| Video/02-1 | HunyuanVideo | GPU ~18 GB |
| Video/02-2 | LTX-Video | GPU ~8 GB |
| Video/02-3 | Wan 2.1/2.2 | GPU ~10 GB |
| Video/02-4 | SVD | GPU ~10 GB |
| Video/03-3 | ComfyUI Video | Docker, nodes video |
| Video/04-3 | Sora 2 API | OPENAI_API_KEY |

## Configuration .env GenAI

Fichier : `MyIA.AI.Notebooks/GenAI/.env`

```bash
# Mode local (Docker) vs remote (myia.io)
LOCAL_MODE=false

# ComfyUI
COMFYUI_API_URL=https://qwen-image-edit.myia.io
COMFYUI_AUTH_TOKEN=<bearer_token_bcrypt>

# OpenAI via OpenRouter
OPENAI_API_KEY=sk-or-v1-...
OPENAI_BASE_URL=https://openrouter.ai/api/v1

# Mode batch pour execution automatisee
BATCH_MODE=false
```

## Configuration generale

- **API keys** : `MyIA.AI.Notebooks/GenAI/.env` (template : `.env.example`)
- **C# settings** : `MyIA.AI.Notebooks/Config/settings.json`
- **Docker** : `docker-configurations/services/comfyui-qwen/.env`

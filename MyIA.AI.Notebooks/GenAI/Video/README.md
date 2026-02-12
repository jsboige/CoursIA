# Video - Generation & Comprehension Video par IA

Serie complete de notebooks pour la generation, la comprehension et l'edition video par IA generative : text-to-video, image-to-video, video understanding, amelioration et workflows de production.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 16 |
| Sous-dossiers | 4 niveaux |
| Kernel | Python 3 |
| Duree totale | ~12-15h |

## Structure

```
Video/
├── 01-Foundation/     # Bases video, comprehension, animation (5 notebooks)
├── 02-Advanced/       # Text-to-video, image-to-video (4 notebooks)
├── 03-Orchestration/  # Multi-modeles, ComfyUI, pipelines (3 notebooks)
└── 04-Applications/   # Education, creatif, production (4 notebooks)
```

## Progression par niveau

### 01-Foundation - Bases Video & Comprehension

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [01-1-Video-Operations-Basics](01-Foundation/01-1-Video-Operations-Basics.ipynb) | moviepy, ffmpeg, decord, codecs | Local | 0 |
| [01-2-GPT-5-Video-Understanding](01-Foundation/01-2-GPT-5-Video-Understanding.ipynb) | GPT-5 video, scenes, Q&A | OpenAI API | 0 |
| [01-3-Qwen-VL-Video-Analysis](01-Foundation/01-3-Qwen-VL-Video-Analysis.ipynb) | Qwen2.5-VL 7B local, grounding | Local GPU | ~18 GB |
| [01-4-Video-Enhancement-ESRGAN](01-Foundation/01-4-Video-Enhancement-ESRGAN.ipynb) | Real-ESRGAN, RIFE interpolation | Local GPU | ~4 GB |
| [01-5-AnimateDiff-Introduction](01-Foundation/01-5-AnimateDiff-Introduction.ipynb) | AnimateDiff, text-to-video basique | Local GPU | ~12 GB |

### 02-Advanced - Modeles generatifs video

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [02-1-HunyuanVideo-Generation](02-Advanced/02-1-HunyuanVideo-Generation.ipynb) | HunyuanVideo, quantization 24GB | Local GPU | ~18 GB |
| [02-2-LTX-Video-Lightweight](02-Advanced/02-2-LTX-Video-Lightweight.ipynb) | LTX-Video, generation rapide | Local GPU | ~8 GB |
| [02-3-Wan-Video-Generation](02-Advanced/02-3-Wan-Video-Generation.ipynb) | Wan 2.1/2.2, prompts FR/EN | Local GPU | ~10 GB |
| [02-4-SVD-Image-to-Video](02-Advanced/02-4-SVD-Image-to-Video.ipynb) | Stable Video Diffusion, animation | Local GPU | ~10 GB |

### 03-Orchestration - Multi-modeles & Pipelines

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [03-1-Multi-Model-Video-Comparison](03-Orchestration/03-1-Multi-Model-Video-Comparison.ipynb) | Benchmark modeles video | Local GPU | ~18 GB |
| [03-2-Video-Workflow-Orchestration](03-Orchestration/03-2-Video-Workflow-Orchestration.ipynb) | Pipelines text->image->video | Mixed | ~18 GB |
| [03-3-ComfyUI-Video-Workflows](03-Orchestration/03-3-ComfyUI-Video-Workflows.ipynb) | Workflows ComfyUI natifs | ComfyUI | ~20 GB |

### 04-Applications - Cas d'usage production

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [04-1-Educational-Video-Generation](04-Applications/04-1-Educational-Video-Generation.ipynb) | Video educative automatique | Mixed | ~12 GB |
| [04-2-Creative-Video-Workflows](04-Applications/04-2-Creative-Video-Workflows.ipynb) | Style transfer, music video | Mixed | ~16 GB |
| [04-3-Sora-API-Cloud-Video](04-Applications/04-3-Sora-API-Cloud-Video.ipynb) | Sora 2 API, cloud vs local | OpenAI API | 0 |
| [04-4-Production-Video-Pipeline](04-Applications/04-4-Production-Video-Pipeline.ipynb) | Pipeline complet bout-en-bout | Mixed | ~18 GB |

## Technologies

| Technologie | Notebooks | Prerequis |
|-------------|-----------|-----------|
| **moviepy / FFmpeg** | 01-1 | Local |
| **OpenAI GPT-5** | 01-2 | `OPENAI_API_KEY` |
| **Qwen2.5-VL** | 01-3 | GPU ~18 GB VRAM |
| **Real-ESRGAN / RIFE** | 01-4 | GPU ~4 GB VRAM |
| **AnimateDiff** | 01-5 | GPU ~12 GB VRAM |
| **HunyuanVideo** | 02-1 | GPU ~18 GB VRAM |
| **LTX-Video** | 02-2 | GPU ~8 GB VRAM |
| **Wan 2.1/2.2** | 02-3 | GPU ~10 GB VRAM |
| **SVD** | 02-4 | GPU ~10 GB VRAM |
| **ComfyUI Video** | 03-3 | Docker, nodes video |
| **OpenAI Sora 2** | 04-3 | `OPENAI_API_KEY` |

## Prerequisites

### API Keys

```bash
# Dans GenAI/.env
OPENAI_API_KEY=sk-...
COMFYUI_AUTH_TOKEN=...   # Pour ComfyUI Video (03-3)
```

### Dependances Python

```bash
pip install -r requirements.txt
pip install -r requirements-video.txt
```

### FFmpeg

FFmpeg doit etre installe sur le systeme :
```bash
# Windows (via winget)
winget install FFmpeg

# Linux
sudo apt install ffmpeg
```

### GPU (pour notebooks locaux)

- Minimum : 4 GB VRAM (Real-ESRGAN, RIFE)
- Recommande : 12+ GB VRAM (AnimateDiff, LTX-Video)
- Optimal : 24 GB VRAM (HunyuanVideo, Wan, tous les notebooks)

## Parcours recommande

```
01-Foundation (bases video, comprehension)
    |
02-Advanced (modeles generatifs specifiques)
    |
03-Orchestration (comparaison, ComfyUI, pipelines)
    |
04-Applications (production, bout-en-bout)
```

| Objectif | Notebooks |
|----------|-----------|
| Decouverte rapide | 01-1, 01-2, 01-5 |
| Generation video | 01-5, 02-1 a 02-4 |
| Comprehension video | 01-2, 01-3 |
| Production | Tous + Audio/04-4 (sync A/V) |

## Licence

Voir la licence du repository principal.

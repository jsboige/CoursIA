# Video - Generation et Comprehension Video par IA

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Audio Sync](../Audio/04-Applications/04-4-Audio-Video-Sync.ipynb)

**La video est le Graal de l'IA generative.** Elle combine l'analyse d'images, la comprehension du temps, la synchronisation audio, et la creation de mouvement coherent. Cette serie vous emmene de la simple comprehension d'une sequence video existante jusqu'a la production d'une video pedagogique complete, generee de bout en bout par des modeles d'IA.

**Fil rouge** : construire un pipeline capable de transformer un script texte en video pedagogique animee, avec voix de synthese et fond musical genere — un defi qui mobilise tous les niveaux de cette serie.

## Progression par niveau

### 01-Foundation - Comprendre la video avant de la generer

On ne peut pas creer ce qu'on ne comprend pas. Ce niveau pose les bases techniques (codecs, ffmpeg, moviepy) et introduit la comprehension video par IA : decomposer une sequence en scenes, repondre a des questions sur le contenu, analyser le mouvement. Vous decouvrirez aussi le surcadrage d'images (ESRGAN) et l'interpolation de frames (RIFE) pour ameliorer la qualite visuelle.

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [01-1-Video-Operations-Basics](01-Foundation/01-1-Video-Operations-Basics.ipynb) | moviepy, ffmpeg, decord, codecs | Local | 0 |
| [01-2-GPT-5-Video-Understanding](01-Foundation/01-2-GPT-5-Video-Understanding.ipynb) | GPT-5 video, scenes, Q&A | OpenAI API | 0 |
| [01-3-Qwen-VL-Video-Analysis](01-Foundation/01-3-Qwen-VL-Video-Analysis.ipynb) | Qwen2.5-VL 7B local, grounding | Local GPU | ~18 GB |
| [01-4-Video-Enhancement-ESRGAN](01-Foundation/01-4-Video-Enhancement-ESRGAN.ipynb) | Real-ESRGAN, RIFE interpolation | Local GPU | ~4 GB |
| [01-5-AnimateDiff-Introduction](01-Foundation/01-5-AnimateDiff-Introduction.ipynb) | AnimateDiff, text-to-video basique | Local GPU | ~12 GB |

### 02-Advanced - Generer du mouvement a partir de texte ou d'images

Ce niveau explore les modeles generatifs video : HunyuanVideo pour la qualite cinematographique (malgre ses 24 GB de VRAM), LTX-Video pour la generation rapide sur des configurations modestes, Wan pour les prompts multilingues, et Stable Video Diffusion pour animer une image existante. Chaque modele a ses forces et ses limites — le but est de les connaitre pour choisir le bon outil au bon moment.

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [02-1-HunyuanVideo-Generation](02-Advanced/02-1-HunyuanVideo-Generation.ipynb) | HunyuanVideo, quantization 24GB | Local GPU | ~18 GB |
| [02-2-LTX-Video-Lightweight](02-Advanced/02-2-LTX-Video-Lightweight.ipynb) | LTX-Video, generation rapide | Local GPU | ~8 GB |
| [02-3-Wan-Video-Generation](02-Advanced/02-3-Wan-Video-Generation.ipynb) | Wan 2.1/2.2, prompts FR/EN | Local GPU | ~10 GB |
| [02-4-SVD-Image-to-Video](02-Advanced/02-4-SVD-Image-to-Video.ipynb) | Stable Video Diffusion, animation | Local GPU | ~10 GB |

### 03-Orchestration - Combiner les modeles dans des pipelines

Un seul modele ne suffit pas pour une production video complete. Ce niveau compare les modeles entre eux, orchestre des pipelines text-to-image-to-video, et exploite ComfyUI pour des workflows natifs plus flexibles. C'est ici que le fil rouge prend forme : un script texte devient scenario, puis images, puis sequence video animee.

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [03-1-Multi-Model-Video-Comparison](03-Orchestration/03-1-Multi-Model-Video-Comparison.ipynb) | Benchmark modeles video | Local GPU | ~18 GB |
| [03-2-Video-Workflow-Orchestration](03-Orchestration/03-2-Video-Workflow-Orchestration.ipynb) | Pipelines text-to-image-to-video | Mixed | ~18 GB |
| [03-3-ComfyUI-Video-Workflows](03-Orchestration/03-3-ComfyUI-Video-Workflows.ipynb) | Workflows ComfyUI natifs | ComfyUI | ~20 GB |

### 04-Applications - Du pipeline a la production

Les trois derniers notebooks et le notebook de synchronisation audio-video concluent le parcours en abordant des cas d'usage reels : generation automatique de contenus educatifs, workflows creatifs (transfert de style, clips musicaux), et l'API Sora 2 d'OpenAI pour la generation cloud. Le pipeline final integre tout ce qui a ete appris dans un systeme bout-en-bout.

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [04-1-Educational-Video-Generation](04-Applications/04-1-Educational-Video-Generation.ipynb) | Video educative automatique | Mixed | ~12 GB |
| [04-2-Creative-Video-Workflows](04-Applications/04-2-Creative-Video-Workflows.ipynb) | Style transfer, music video | Mixed | ~16 GB |
| [04-3-Sora-API-Cloud-Video](04-Applications/04-3-Sora-API-Cloud-Video.ipynb) | Sora 2 API, cloud vs local | OpenAI API | 0 |
| [04-4-Production-Video-Pipeline](04-Applications/04-4-Production-Video-Pipeline.ipynb) | Pipeline complet bout-en-bout | Mixed | ~18 GB |

## Ce que vous saurez faire

- **Comprendre** une sequence video : decomposition en scenes, Q&A sur le contenu, analyse temporelle
- **Generer** des videos a partir de texte ou d'images : choix du modele adapte a votre materiel
- **Orchestrer** des pipelines multi-modeles : scenario texte vers video complete
- **Produire** des contenus video educatifs ou creatifs de bout en bout
- **Comparer** les approches cloud (Sora) et locales (HunyuanVideo, Wan) en termes de qualite, cout et latence

## Technologies couvertes

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
COMFYUI_AUTH_TOKEN=...
```

### GPU (pour notebooks locaux)

- **Minimum** : 4 GB VRAM (Real-ESRGAN, RIFE)
- **Recommande** : 12+ GB VRAM (AnimateDiff, LTX-Video)
- **Optimal** : 24 GB VRAM (HunyuanVideo, Wan, tous les notebooks)

### FFmpeg

FFmpeg doit etre installe sur le systeme :

```bash
# Windows (via winget)
winget install FFmpeg
```

## Parcours recommande

| Objectif | Notebooks |
|----------|-----------|
| Decouverte rapide | 01-1, 01-2, 01-5 |
| Generation video | 01-5, 02-1 a 02-4 |
| Comprehension video | 01-2, 01-3 |
| Production complete | Tous + Audio/04-4 (sync A/V) |

## Licence

Voir la licence du repository principal.

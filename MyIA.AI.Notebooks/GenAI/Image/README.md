# Image - Generation d'Images par IA

Serie complete de notebooks pour la generation et l'edition d'images par IA generative, couvrant les modeles de base jusqu'aux workflows de production.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 19 |
| Sous-dossiers | 5 (4 niveaux + examples) |
| Kernel | Python 3 |
| Duree totale | ~6-8h |

## Structure

```
Image/
├── 01-Foundation/     # Modeles de base (5 notebooks)
├── 02-Advanced/       # Modeles avances (4 notebooks)
├── 03-Orchestration/  # Multi-modeles (3 notebooks)
├── 04-Applications/   # Production (4 notebooks)
└── examples/          # Cas d'usage (3 notebooks)
```

## Progression par niveau

### 01-Foundation - Modeles de base

| Notebook | Contenu | Service |
|----------|---------|---------|
| [01-1-OpenAI-DALL-E-3](01-Foundation/01-1-OpenAI-DALL-E-3.ipynb) | Generation avec DALL-E 3 | OpenAI API |
| [01-2-GPT-5-Image-Generation](01-Foundation/01-2-GPT-5-Image-Generation.ipynb) | Generation avec GPT-5 | OpenAI API |
| [01-3-Basic-Image-Operations](01-Foundation/01-3-Basic-Image-Operations.ipynb) | Operations de base | PIL/OpenCV |
| [01-4-Forge-SD-XL-Turbo](01-Foundation/01-4-Forge-SD-XL-Turbo.ipynb) | Stable Diffusion XL Turbo | ComfyUI |
| [01-5-Qwen-Image-Edit](01-Foundation/01-5-Qwen-Image-Edit.ipynb) | Introduction Qwen | ComfyUI |

[README 01-Foundation](01-Foundation/README.md)

### 02-Advanced - Modeles avances

| Notebook | Contenu | Service |
|----------|---------|---------|
| [02-1-Qwen-Image-Edit-2509](02-Advanced/02-1-Qwen-Image-Edit-2509.ipynb) | Edition avancee Qwen | ComfyUI |
| [02-2-FLUX-1-Advanced-Generation](02-Advanced/02-2-FLUX-1-Advanced-Generation.ipynb) | Generation FLUX | ComfyUI |
| [02-3-Stable-Diffusion-3-5](02-Advanced/02-3-Stable-Diffusion-3-5.ipynb) | SD 3.5 | ComfyUI |
| [02-4-Z-Image-Lumina2](02-Advanced/02-4-Z-Image-Lumina2.ipynb) | Z-Image/Lumina | ComfyUI |

[README 02-Advanced](02-Advanced/README.md)

### 03-Orchestration - Multi-modeles

| Notebook | Contenu |
|----------|---------|
| [03-1-Multi-Model-Comparison](03-Orchestration/03-1-Multi-Model-Comparison.ipynb) | Comparaison multi-modeles |
| [03-2-Workflow-Orchestration](03-Orchestration/03-2-Workflow-Orchestration.ipynb) | Orchestration de workflows |
| [03-3-Performance-Optimization](03-Orchestration/03-3-Performance-Optimization.ipynb) | Optimisation performance |

[README 03-Orchestration](03-Orchestration/README.md)

### 04-Applications - Production

| Notebook | Contenu |
|----------|---------|
| [04-1-Educational-Content-Generation](04-Applications/04-1-Educational-Content-Generation.ipynb) | Contenu educatif |
| [04-2-Creative-Workflows](04-Applications/04-2-Creative-Workflows.ipynb) | Workflows creatifs |
| [04-3-Production-Integration](04-Applications/04-3-Production-Integration.ipynb) | Integration production |
| [04-4-Cross-Stitch-Pattern-Maker-Legacy](04-Applications/04-4-Cross-Stitch-Pattern-Maker-Legacy.ipynb) | Point de croix (legacy) |

[README 04-Applications](04-Applications/README.md)

### examples/ - Cas d'usage

| Notebook | Domaine |
|----------|---------|
| [history-geography](examples/history-geography.ipynb) | Histoire-Geographie |
| [literature-visual](examples/literature-visual.ipynb) | Litterature |
| [science-diagrams](examples/science-diagrams.ipynb) | Diagrammes scientifiques |

## Technologies

| Technologie | Notebooks | Prerequis |
|-------------|-----------|-----------|
| **OpenAI DALL-E 3** | 01-1, 01-2 | `OPENAI_API_KEY` |
| **ComfyUI + Qwen** | 01-4, 01-5, 02-1 | Docker, ~29GB VRAM |
| **ComfyUI + FLUX** | 02-2 | Docker GPU |
| **ComfyUI + SD 3.5** | 02-3 | Docker GPU |
| **Z-Image/Lumina** | 02-4 | Docker, ~10GB VRAM |

## Prerequisites

### API Keys

```bash
# Dans GenAI/.env
OPENAI_API_KEY=sk-...
COMFYUI_BEARER_TOKEN=...
```

### Docker Services

```bash
cd docker-configurations/services/comfyui-qwen
docker-compose up -d
```

Acces : http://localhost:8188

## Parcours recommande

```
01-Foundation (bases)
    |
02-Advanced (modeles specifiques)
    |
03-Orchestration (comparaison, workflows)
    |
04-Applications (production)
```

| Objectif | Notebooks |
|----------|-----------|
| Decouverte rapide | 01-1, 01-3 |
| Generation avancee | 01-1 a 02-4 |
| Production | Tous + 03 + 04 |

## Licence

Voir la licence du repository principal.

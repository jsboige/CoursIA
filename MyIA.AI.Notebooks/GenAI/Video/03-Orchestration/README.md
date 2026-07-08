# 03-Orchestration - Multi-modèles & Workflows Vidéo

[← Video Advanced](../02-Advanced/) | [↑ Video](../README.md) | [→ Video Applications](../04-Applications/)

Ce module couvre l'orchestration de plusieurs modèles vidéo, les workflows complexes, et l'intégration ComfyUI.

**Dans le cadre du fil rouge pipeline vidéo pédagogique** : les briques existent, il faut les assembler. [03-1](03-1-Multi-Model-Video-Comparison.ipynb) compare les modeaux pour choisir le meilleur selon le matériel et le contexte. [03-2](03-2-Video-Workflow-Orchestration.ipynb) construit le pipeline text-to-image-to-video qui constitue le coeur du générateur. [03-3](03-3-ComfyUI-Video-Workflows.ipynb) utilise ComfyUI pour des workflows natifs plus flexibles.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 3 |
| Kernel | Python 3 |
| Durée estimée | ~4-6h |
| GPU requis | Variable |

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------ |
| 1 | [03-1-Multi-Model-Video-Comparison](03-1-Multi-Model-Video-Comparison.ipynb) | Comparatif modèles | Mixed | Variable |
| 2 | [03-2-Video-Workflow-Orchestration](03-2-Video-Workflow-Orchestration.ipynb) | Orchestration workflows | ComfyUI | Variable |
| 3 | [03-3-ComfyUI-Video-Workflows](03-3-ComfyUI-Video-Workflows.ipynb) | ComfyUI spécifique | ComfyUI | Variable |

## Prérequis

### Docker Services
```bash
cd docker-configurations/services/comfyui-qwen
docker-compose up -d
```
Accès : http://localhost:8188

### Dépendances
```bash
pip install -r requirements.txt
pip install -r requirements-video.txt
pip install -r requirements-comfyui.txt
```

## Progression recommandée

1. **03-1-Multi-Model-Video-Comparison** - Comparatif des modèles
2. **03-2-Video-Workflow-Orchestration** - Création de workflows
3. **03-3-ComfyUI-Video-Workflows** - Intégration ComfyUI

## Concepts clés

### Multi-Model Comparison
- **Critères** : Qualité, temps, ressources, contrôle
- **Modèles** : HunyuanVideo, LTX, Wan, SVD
- **Métriques** : FPS, résolution, artefacts

### Workflow Orchestration
- **Patterns** : Pipeline video, batch processing
- **Outils** : Python asyncio, multiprocessing
- **Optimisation** : Caching, parallélisation

### ComfyUI Integration
- **Nodes** : Video-specific nodes
- **Workflow** : End-to-end video generation
- **Scaling** : Gestion de la mémoire

## Architecture

```
Input → Model Router → Processing → Output
    ↓         ↓          ↓         ↓
  Analysis  Selection   Pipeline  Validation
```

## Galerie

Sorties réelles des notebooks : workflow d'orchestration vidéo ([03-2](03-2-Video-Workflow-Orchestration.ipynb)) et workflow ComfyUI de génération vidéo ([03-3](03-3-ComfyUI-Video-Workflows.ipynb)).

<table>
<tr>
<td align="center"><img src="assets/readme/vid3-workflow1.webp" alt="Diagramme d'un workflow d'orchestration vidéo" width="400"/><br/><sub>Workflow d'orchestration vidéo — vue d'ensemble (<a href="03-2-Video-Workflow-Orchestration.ipynb">03-2</a>)</sub></td>
<td align="center"><img src="assets/readme/vid3-workflow2.webp" alt="Panorama d'un pipeline vidéo multi-étapes" width="400"/><br/><sub>Workflow vidéo — panorama du pipeline (<a href="03-2-Video-Workflow-Orchestration.ipynb">03-2</a>)</sub></td>
</tr>
<tr>
<td align="center"><img src="assets/readme/vid3-frame1.webp" alt="Frame vidéo générée, étape 1 du workflow" width="400"/><br/><sub>Frame vidéo générée — étape 1 (<a href="03-2-Video-Workflow-Orchestration.ipynb">03-2</a>)</sub></td>
<td align="center"><img src="assets/readme/vid3-frame2.webp" alt="Frame vidéo générée, étape 2 du workflow" width="400"/><br/><sub>Frame vidéo générée — étape 2 (<a href="03-2-Video-Workflow-Orchestration.ipynb">03-2</a>)</sub></td>
</tr>
<tr>
<td align="center" colspan="2"><img src="assets/readme/vid3-comfyui.webp" alt="Workflow ComfyUI de bout en bout pour la génération vidéo" width="640"/><br/><sub>Workflow ComfyUI — génération vidéo de bout en bout (<a href="03-3-ComfyUI-Video-Workflows.ipynb">03-3</a>)</sub></td>
</tr>
</table>

Provenance et poids de chaque figure : [`assets/readme/MANIFEST.md`](assets/readme/MANIFEST.md).

## Ressources

- [Documentation Video principale](../README.md)
- [Guide ComfyUI](../../00-GenAI-Environment/README.md)
- [GenAI Services](../../../../docs/genai/genai-services.md)

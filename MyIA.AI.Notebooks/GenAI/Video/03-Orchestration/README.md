# 03-Orchestration - Multi-modèles & Workflows Vidéo

[← Video Advanced](../02-Advanced/) | [↑ Video](../README.md) | [→ Video Applications](../04-Applications/)

Ce module couvre l'orchestration de plusieurs modèles vidéo, les workflows complexes, et l'intégration ComfyUI.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 3 |
| Kernel | Python 3 |
| Duree estimee | ~4-6h |
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

## Ressources

- [Documentation Video principale](../README.md)
- [Guide ComfyUI](../../00-GenAI-Environment/README.md)
- [Production Best Practices](../../docs/)
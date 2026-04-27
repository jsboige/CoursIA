# 02-Advanced - Génération Vidéo Avancée

[← Video Foundation](../01-Foundation/) | [↑ Video](../README.md) | [→ Video Orchestration](../03-Orchestration/)

Ce module explore les modèles de génération vidéo de pointe : HunyuanVideo, LTX Video, Wan Video, et SVD.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 4 |
| Kernel | Python 3 |
| Duree estimee | ~5-7h |
| GPU requis | 8-24GB |

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------ |
| 1 | [02-1-HunyuanVideo-Generation](02-1-HunyuanVideo-Generation.ipynb) | Génération Hunyuan | Local GPU | ~18GB |
| 2 | [02-2-LTX-Video-Lightweight](02-2-LTX-Video-Lightweight.ipynb) | Génération légère LTX | Local GPU | ~8GB |
| 3 | [02-3-Wan-Video-Generation](02-3-Wan-Video-Generation.ipynb) | Génération Wan | Local GPU | ~10GB |
| 4 | [02-4-SVD-Image-to-Video](02-4-SVD-Image-to-Video.ipynb) | SVD (Image → Vidéo) | ComfyUI | ~10GB |

## Prérequis

### Docker Services
```bash
cd docker-configurations/services/comfyui-qwen
docker-compose up -d
```
Accès : http://localhost:8188

### GPU Requirements
- **Minimum** : 8 GB VRAM (LTX Video)
- **Recommandé** : 10-12 GB VRAM (SVD, Wan Video)
- **Optimal** : 18+ GB VRAM (HunyuanVideo)

### Dépendances
```bash
pip install -r requirements.txt
pip install -r requirements-video.txt
pip install -r requirements-comfyui.txt
```

## Progression recommandée

1. **02-1-HunyuanVideo-Generation** - Qualité maximale
2. **02-2-LTX-Video-Lightweight** - Performance/équilibre
3. **02-3-Wan-Video-Generation** - Alternative rapide
4. **02-4-SVD-Image-to-Video** - Animation d'images

## Technologies clés

### HunyuanVideo (Tencent)
- **Spécialité** : Vidéo haute qualité, réaliste
- **Durée** : Jusqu'à plusieurs secondes
- **VRAM** : ~18GB

### LTX Video (Lightweight)
- **Spécialité** : Rapidité, efficacité
- **Durée** : Courtes vidéos
- **VRAM** : ~8GB

### Wan Video
- **Spécialité** : Animation, mouvement fluide
- **Durée** : Courts clips
- **VRAM** : ~10GB

### SVD (Stable Video Diffusion)
- **Spécialité** : Image → Vidéo
- **Durée** : Courtes animations
- **VRAM** : ~10GB

## Comparatif

| Modèle | Qualité | Vitesse | VRAM | Cas d'usage |
|--------|---------|---------|------|-------------|
| HunyuanVideo | Exceptionnelle | Lent | ~18GB | Production premium |
| LTX Video | Bonne | Rapide | ~8GB | Prototypage rapide |
| Wan Video | Bonne | Moyen | ~10GB | Animation fluide |
| SVD | Variable | Moyen | ~10GB | Animation d'images |

## Ressources

- [Documentation Video principale](../README.md)
- [Guide ComfyUI](../../00-GenAI-Environment/README.md)
- [Architecture ComfyUI](../../docs/COMFYUI-ARCHITECTURE.md)
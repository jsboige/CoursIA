# 02-Advanced - Modèles avancés

[← Image Foundation](../01-Foundation/) | [↑ Image](../README.md) | [→ Image Orchestration](../03-Orchestration/)

Ce module explore les modèles de pointe : Qwen Image Edit avancé, FLUX, SD 3.5, et Z-Image/Lumina.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 4 |
| Kernel | Python 3 |
| Duree estimee | ~4-6h |
| GPU requis | 10-29GB |

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------ |
| 1 | [02-1-Qwen-Image-Edit-2509](02-1-Qwen-Image-Edit-2509.ipynb) | Édition avancée Qwen | ComfyUI | ~29GB |
| 2 | [02-2-FLUX-1-Advanced-Generation](02-2-FLUX-1-Advanced-Generation.ipynb) | Génération FLUX | ComfyUI | Variable |
| 3 | [02-3-Stable-Diffusion-3-5](02-3-Stable-Diffusion-3-5.ipynb) | SD 3.5 | ComfyUI | Variable |
| 4 | [02-4-Z-Image-Lumina2](02-4-Z-Image-Lumina2.ipynb) | Z-Image/Lumina | ComfyUI | ~10GB |

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
pip install -r requirements-comfyui.txt
```

## Progression recommandée

1. **02-1-Qwen-Image-Edit-2509** - Édition multimodale avancée
2. **02-2-FLUX-1-Advanced-Generation** - Génération de haute qualité
3. **02-3-Stable-Diffusion-3.5** - SD 3.5 pour contrôle fin
4. **02-4-Z-Image-Lumina2** - Modèle léger et rapide

## Technologies clés

### Qwen Image Edit 2509
- **Architecture** : Diffusion conditioned
- **Points forts** : Édition précise, texte dans l'image
- **VRAM** : ~29GB (VAE 16 canaux)

### FLUX 1
- **Architecture** : Transformer-based
- **Points forts** : Consistency, contrôle prompts
- **VRAM** : Variable

### Stable Diffusion 3.5
- **Architecture** : Diffusion classique
- **Points forts** : Écosystème mature, contrôle contrôles
- **VRAM** : Variable

### Z-Image/Lumina
- **Architecture** : LuminaDiffusers
- **Points forts** : Vitesse, qualité légère
- **VRAM** : ~10GB

## Comparatif

| Modèle | Spécialité | VRAM | Qualité | Vitesse |
|--------|------------|------|---------|--------|
| Qwen | Édition | ~29GB | Excellent | Lent |
| FLUX | Génération | Variable | Exceptionnel | Moyen |
| SD 3.5 | Polyvalent | Variable | Bon | Rapide |
| Z-Image | Léger | ~10GB | Bon | Très rapide |

## Ressources

- [Documentation Image principale](../README.md)
- [Guide ComfyUI](../../00-GenAI-Environment/README.md)
- [Architecture ComfyUI](../../docs/COMFYUI-ARCHITECTURE.md)
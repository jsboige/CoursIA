# 01-Foundation - Modèles de base

[← Documentation Image](../README.md) | [↑ ..](../README.md) | [→ Image Advanced](../02-Advanced/)

Ce module couvre les fondamentaux de la génération d'images par IA : modèles cloud, ComfyUI, et opérations de base.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 5 |
| Kernel | Python 3 |
| Duree estimee | ~3-4h |
| GPU requis | 0-29GB |

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------ |
| 1 | [01-1-OpenAI-DALL-E-3](01-1-OpenAI-DALL-E-3.ipynb) | Génération avec DALL-E 3 | OpenAI API | 0 |
| 2 | [01-2-GPT-5-Image-Generation](01-2-GPT-5-Image-Generation.ipynb) | Génération avec GPT-5 | OpenAI API | 0 |
| 3 | [01-3-Basic-Image-Operations](01-3-Basic-Image-Operations.ipynb) | Opérations de base | PIL/OpenCV | 0 |
| 4 | [01-4-Forge-SD-XL-Turbo](01-4-Forge-SD-XL-Turbo.ipynb) | Stable Diffusion XL Turbo | ComfyUI | Variable |
| 5 | [01-5-Qwen-Image-Edit](01-5-Qwen-Image-Edit.ipynb) | Introduction Qwen | ComfyUI | ~29GB |

## Prérequis

### API Keys
```bash
# Dans GenAI/.env
OPENAI_API_KEY=sk-...
COMFYUI_BEARER_TOKEN=...
```

### Docker Services (optionnel)
```bash
cd docker-configurations/services/comfyui-qwen
docker-compose up -d
```
Accès : http://localhost:8188

## Progression recommandée

1. **01-1-OpenAI-DALL-E-3** - Introduction rapide à la génération d'images
2. **01-2-GPT-5-Image-Generation** - Génération multimodale avec texte
3. **01-3-Basic-Image-Operations** - Manipulation d'images locale
4. **01-4-Forge-SD-XL-Turbo** - Modèle open source via ComfyUI
5. **01-5-Qwen-Image-Edit** - Édition d'images avancée

## Points clés

- **Cloud vs Local** : OpenAI (facile, API) vs ComfyUI (puissant, local)
- **Formats** : PNG, JPEG, WebP supportés
- **Qualité** : DALL-E 3 > GPT-5 > SD-XL Turbo
- **Flexibilité** : SD-XL Turbo plus paramétrable que les modèles cloud

## Ressources

- [Documentation Image principale](../README.md)
- [Guide ComfyUI](../../00-GenAI-Environment/README.md)
# 01-Foundation - Modèles de base

[← Documentation Image](../README.md) | [↑ ..](../README.md) | [→ Image Advanced](../02-Advanced/)

Ce module couvre les fondamentaux de la génération d'images par IA : modèles cloud, ComfyUI, et opérations de base.

**Dans le cadre du fil rouge contenu visuel éducatif** : avant de produire des visuels, il faut savoir générer une image à partir d'un texte. [01-1](01-1-OpenAI-DALL-E-3.ipynb) et [01-2](01-2-GPT-5-Image-Generation.ipynb) couvrent les API cloud (simples et immédiates). [01-4](01-4-Forge-SD-XL-Turbo.ipynb) et [01-5](01-5-Qwen-Image-Edit.ipynb) passent en local via ComfyUI pour le contrôle fin. [01-3](01-3-Basic-Image-Operations.ipynb) donne les bases de manipulation (PIL, OpenCV) utiles pour comprendre ce que font les modèles.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 5 |
| Kernel | Python 3 |
| Durée estimée | ~3-4h |
| GPU requis | 0-29GB |

## Aperçu — les modèles de base en images

Ce module pose les fondamentaux : génération via API cloud (DALL-E 3), génération locale auto-hébergée (Stable Diffusion via Forge), et édition ciblée d'une image existante (Qwen Image Edit). La galerie ci-dessous présente des sorties réelles extraites des notebooks.

<table>
<tr>
<td align="center"><img src="assets/readme/img1-dalle3.webp" alt="Génération DALL-E 3 via API OpenAI" width="400"/><br/><sub>DALL-E 3 API (01-1)</sub></td>
<td align="center"><img src="assets/readme/img1-forge-gen.webp" alt="Génération SD XL Turbo via Forge" width="400"/><br/><sub>SD Forge (01-4)</sub></td>
</tr>
<tr>
<td align="center"><img src="assets/readme/img1-forge-gen2.webp" alt="Génération SD Forge — variante" width="400"/><br/><sub>SD Forge variante (01-4)</sub></td>
<td align="center"><img src="assets/readme/img1-forge-gen3.webp" alt="Génération SD Forge — composition" width="400"/><br/><sub>SD Forge composition (01-4)</sub></td>
</tr>
<tr>
<td align="center"><img src="assets/readme/img1-qwen-edit.png" alt="Édition Qwen Image Edit — avant" width="400"/><br/><sub>Qwen Edit (01-5)</sub></td>
<td align="center"><img src="assets/readme/img1-qwen-edit2.png" alt="Édition Qwen Image Edit — panorama" width="400"/><br/><sub>Qwen Edit panorama (01-5)</sub></td>
</tr>
</table>

Provenance et poids de chaque figure : [`assets/readme/MANIFEST.md`](assets/readme/MANIFEST.md).

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------ |
| 1 | [01-1-OpenAI-DALL-E-3](01-1-OpenAI-DALL-E-3.ipynb) | Génération avec gpt-image-1 (DALL-E 3 retiré) | OpenAI API | 0 |
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
- **Qualité** : gpt-image-1 > GPT-5 > SD-XL Turbo
- **Flexibilité** : SD-XL Turbo plus paramétrable que les modèles cloud

## Ressources

- [Documentation Image principale](../README.md)
- [Guide ComfyUI](../../00-GenAI-Environment/README.md)
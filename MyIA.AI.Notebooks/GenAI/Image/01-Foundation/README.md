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

Ce module pose les fondamentaux : génération via API cloud (DALL-E 3), génération locale auto-hébergée (Stable Diffusion via Forge), et édition ciblée d'une image existante (Qwen Image Edit). Plutôt qu'une galerie séparée du propos, chaque sortie réelle est placée ci-dessous au plus près du notebook qui la produit. Provenance et poids de chaque figure : [`assets/readme/MANIFEST.md`](assets/readme/MANIFEST.md).

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------ |
| 1 | [01-1-OpenAI-DALL-E-3](01-1-OpenAI-DALL-E-3.ipynb) | Génération avec gpt-image-1 (DALL-E 3 retiré) | OpenAI API | 0 |
| 2 | [01-2-GPT-5-Image-Generation](01-2-GPT-5-Image-Generation.ipynb) | Génération avec GPT-5 | OpenAI API | 0 |
| 3 | [01-3-Basic-Image-Operations](01-3-Basic-Image-Operations.ipynb) | Opérations de base | PIL/OpenCV | 0 |
| 4 | [01-4-Forge-SD-XL-Turbo](01-4-Forge-SD-XL-Turbo.ipynb) | Stable Diffusion XL Turbo | ComfyUI | Variable |
| 5 | [01-5-Qwen-Image-Edit](01-5-Qwen-Image-Edit.ipynb) | Introduction Qwen | ComfyUI | ~29GB |

**[01-1](01-1-OpenAI-DALL-E-3.ipynb) — API cloud.** Le point d'entrée le plus immédiat : un prompt, une clé, et gpt-image-1 renvoie un visuel en ~19 s :

<p align="center">
  <a href="01-1-OpenAI-DALL-E-3.ipynb"><img src="assets/readme/img1-dalle3.webp" alt="Paysage urbain futuriste au coucher de soleil avec voitures volantes et lumières néon généré par gpt-image-1" width="380"/></a><br>
  <em>gpt-image-1 : ville futuriste au coucher de soleil, voitures volantes, néons reflétés sur les immeubles de verre (1024×1024 requis, redimensionné à 746×789).</em>
</p>

**[01-4](01-4-Forge-SD-XL-Turbo.ipynb) — Génération locale via Forge.** Mêmes prompts, mais sur GPU auto-hébergé via Stable Diffusion XL Turbo : le mode 4-steps produit un rendu acceptable en ~18 s, et fixer la seed garantit la reproductibilité :

<p align="center">
  <a href="01-4-Forge-SD-XL-Turbo.ipynb"><img src="assets/readme/img1-forge-gen.webp" alt="Paysage de montagne serein au coucher de soleil, éclairage golden hour, photoréaliste, généré par SDXL Turbo via Forge" width="320"/></a>
  <a href="01-4-Forge-SD-XL-Turbo.ipynb"><img src="assets/readme/img1-forge-gen2.webp" alt="Ville futuriste la nuit, lumières néon, style cyberpunk, générée en 4 steps SDXL Turbo" width="320"/></a><br>
  <em>SDXL Turbo : paysage de montagne « golden hour » (gauche) et ville cyberpunk en mode 4-steps (droite) — premier exemple de génération locale via Forge.</em>
</p>

<p align="center">
  <a href="01-4-Forge-SD-XL-Turbo.ipynb"><img src="assets/readme/img1-forge-gen3.webp" alt="Forêt mystique aux champignons lumineux générée avec seed fixe 42 pour reproductibilité" width="340"/></a><br>
  <em>SDXL Turbo : forêt mystique (seed fixe 42) — la seed garantit le même résultat à chaque exécution.</em>
</p>

**[01-5](01-5-Qwen-Image-Edit.ipynb) — Édition via ComfyUI.** Qwen Image Edit (workflow Phase 29 : VAE 16 canaux + CLIP sd3 + UNET fp8 + ModelSamplingAuraFlow shift=3.0 + CFGNorm 1.0) : le hello-world atteste que le service est joignable (~277 s, ~29 GB VRAM), puis le workflow image-to-image édite un visuel existant (~170 s) :

<p align="center">
  <a href="01-5-Qwen-Image-Edit.ipynb"><img src="assets/readme/img1-qwen-edit.png" alt="Génération hello-world de Qwen Image Edit (modèle Qwen 2.5-VL) via workflow ComfyUI" width="320"/></a>
  <a href="01-5-Qwen-Image-Edit.ipynb"><img src="assets/readme/img1-qwen-edit2.png" alt="Workflow image-to-image Qwen (VAE 16 canaux + CLIP sd3 + UNET fp8 + ModelSamplingAuraFlow shift 3.0 + CFGNorm 1.0) sur image placeholder" width="320"/></a><br>
  <em>Qwen Image Edit : hello-world (gauche, ~277 s) puis workflow image-to-image Phase 29 (droite, ~170 s).</em>
</p>

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
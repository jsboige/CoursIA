# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

Les images GenAI generees etant riches en details, certaines figures depassent 200 KB meme en PNG a 500 px. Ces figures basculent en WebP (fallback greenlight ai-01 #5654) : gain net ~3-4x, dimensions conservees.

## dalle3-cover.webp

- **Source** : notebook `01-Foundation/01-1-OpenAI-DALL-E-3.ipynb` (cellule 14, output 3)
- **Alt-text (FR)** : Couverture : portrait illustré généré par DALL-E 3 depuis un prompt textuel.
- **Poids** : 64.0 KB (WebP fallback max-dim 800 (PNG >200KB meme a 500px))

## forge-sdxl-turbo.webp

- **Source** : notebook `01-Foundation/01-4-Forge-SD-XL-Turbo.ipynb` (cellule 22, output 2)
- **Alt-text (FR)** : Image SD XL Turbo : génération locale rapide via ComfyUI sur GPU auto-hébergé.
- **Poids** : 47.0 KB (WebP fallback max-dim 800 (PNG >200KB meme a 500px))

## qwen-edit-panel.png

- **Source** : notebook `01-Foundation/01-5-Qwen-Image-Edit.ipynb` (cellule 18, output 3)
- **Alt-text (FR)** : Édition Qwen Image Edit : panneau avant/après d'inpainting sur une zone masquée.
- **Poids** : 50.6 KB (natif)

## flux1-advanced.webp

- **Source** : notebook `02-Advanced/02-2-FLUX-1-Advanced-Generation.ipynb` (cellule 9, output 9)
- **Alt-text (FR)** : Génération FLUX.1 : rendu photo-réaliste haute qualité avec contrôle de prompt avancé.
- **Poids** : 195.0 KB (WebP fallback max-dim 800 (PNG >200KB meme a 500px))

## lumina2-zimage.webp

- **Source** : notebook `02-Advanced/02-4-Z-Image-Lumina2.ipynb` (cellule 11, output 3)
- **Alt-text (FR)** : Z-Image / Lumina2 : génération diffuse alternative, comparée aux modèles précédents.
- **Poids** : 61.1 KB (WebP fallback max-dim 800 (PNG >200KB meme a 500px))

## workflow-orchestration.png

- **Source** : notebook `03-Orchestration/03-2-Workflow-Orchestration.ipynb` (cellule 21, output 2)
- **Alt-text (FR)** : Workflow ComfyUI orchestré : chaîne de nœuds (Sampler, VAE, upscaler) pour un pipeline de production.
- **Poids** : 8.3 KB (natif)

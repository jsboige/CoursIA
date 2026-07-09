# Galerie README — Image 01-Foundation (modèles de base)

Provenance de chaque figure (convention `extract_readme_figures.py` L132 : index ALL-CELLS).
Toutes les figures sont extraites des **outputs déjà committés** des notebooks (C.3 — aucune re-exécution).
Bornes EPIC #5654 P1 respectées : ≤200 KB/fichier, ≤1200 px max-dim.

Les images générées par les modèles GenAI étant photographiques (denses), le fallback **WebP** (EPIC P2) est utilisé pour 4 figures où le PNG natif dépassait la borne — gain net documenté ci-dessous.

| Figure | Notebook source | Cellule | Output | Format | Dimensions | Poids | Alt-text FR |
|--------|-----------------|---------|--------|--------|------------|-------|-------------|
| `img1-dalle3.webp` | `01-1-OpenAI-DALL-E-3.ipynb` | 14 | 3 | WebP | 746×789 | 64,0 KB | Paysage urbain futuriste au coucher de soleil (voitures volantes, néons, hologrammes) généré par gpt-image-1 |
| `img1-forge-gen.webp` | `01-4-Forge-SD-XL-Turbo.ipynb` | 10 | 2 | WebP | 761×789 | 51,3 KB | Paysage de montagne au coucher de soleil (« golden hour », photoréaliste) généré par SDXL Turbo via Forge |
| `img1-forge-gen2.webp` | `01-4-Forge-SD-XL-Turbo.ipynb` | 12 | 2 | WebP | 766×790 | 45,2 KB | Ville cyberpunk nocturne (néons) en mode 4-steps Turbo |
| `img1-forge-gen3.webp` | `01-4-Forge-SD-XL-Turbo.ipynb` | 18 | 1 | WebP | 568×590 | 43,4 KB | Forêt mystique aux champignons lumineux avec seed fixe 42 (génération reproductible) |
| `img1-qwen-edit.png` | `01-5-Qwen-Image-Edit.ipynb` | 10 | 2 | PNG | 370×390 | 131,0 KB | Génération hello-world du workflow ComfyUI Qwen Image Edit 2509 (test de connectivité au service, ~277s) |
| `img1-qwen-edit2.png` | `01-5-Qwen-Image-Edit.ipynb` | 18 | 3 | PNG | 1041×490 | 50,6 KB | Workflow image-to-image Qwen Phase 29 (VAE 16-ch + CLIP sd3 + UNET fp8 + ModelSamplingAuraFlow shift 3.0 + CFGNorm 1.0) |

**Diversité couverte** : 3 modèles fondamentaux (DALL-E 3 API, Stable Diffusion via Forge, Qwen Image Edit). Total : 6 figures, 385,5 KB, max 131,0 KB/fichier. WebP fallback (P2) justifié : sources natives 0,5–0,9 MB (images photographiques denses).

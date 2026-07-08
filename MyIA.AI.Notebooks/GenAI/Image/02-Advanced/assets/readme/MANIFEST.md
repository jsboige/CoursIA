# Galerie README — Image 02-Advanced (modèles avancés)

Provenance de chaque figure (convention `extract_readme_figures.py` L132 : index ALL-CELLS).
Toutes les figures sont extraites des **outputs déjà committés** des notebooks (C.3 — aucune re-exécution).
Bornes EPIC #5654 P1 respectées : ≤200 KB/fichier, ≤1200 px max-dim.

Les images générées par les modèles GenAI étant photographiques (denses), le fallback **WebP** (EPIC P2) est utilisé pour 3 figures où le PNG natif dépassait la borne — gain net documenté ci-dessous.

| Figure | Notebook source | Cellule | Output | Format | Dimensions | Poids | Alt-text FR |
|--------|-----------------|---------|--------|--------|------------|-------|-------------|
| `img2-qwen-edit.png` | `02-1-Qwen-Image-Edit-2509.ipynb` | 17 | 1 | PNG | 900×242 | 170,5 KB | Édition Qwen Image Edit — panorama avant/après |
| `img2-qwen-edit2.webp` | `02-1-Qwen-Image-Edit-2509.ipynb` | 24 | 5 | WebP | 780×800 | 66,8 KB | Édition Qwen — variante de prompt |
| `img2-flux-gen.webp` | `02-2-FLUX-1-Advanced-Generation.ipynb` | 9 | 9 | WebP | 781×800 | 195,0 KB | Génération FLUX-1 — image photoréaliste |
| `img2-flux-gen2.png` | `02-2-FLUX-1-Advanced-Generation.ipynb` | 15 | 9 | PNG | 500×329 | 154,1 KB | Génération FLUX-1 — composition alternative |
| `img2-zimage-lumina.webp` | `02-4-Z-Image-Lumina2.ipynb` | 11 | 3 | WebP | 784×800 | 61,1 KB | Génération Z-Image/Lumina2 — prototypage rapide |
| `img2-bonsai-ternary.png` | `02-5-Bonsai-Image-Ternary.ipynb` | 6 | 0 | PNG | 885×590 | 34,1 KB | Bonsai ternaire 1,58-bit — génération efficace |

**Diversité couverte** : 4 modèles avancés (Qwen Edit, FLUX-1, Z-Image/Lumina2, Bonsai ternaire). Total : 6 figures, 681,6 KB, max 195,0 KB/fichier. WebP fallback (P2) justifié : sources natives 0,3–2,2 MB (images photographiques denses).

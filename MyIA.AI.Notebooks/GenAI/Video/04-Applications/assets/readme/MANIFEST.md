# Galerie README — Video 04-Applications (cas d'usage production)

Provenance de chaque figure (convention `extract_readme_figures.py` L132 : index ALL-CELLS).
Toutes les figures sont extraites des **outputs déjà committés** des notebooks (C.3 — aucune re-exécution).
Bornes EPIC #5654 P1 respectées : ≤200 KB/fichier, ≤1200 px max-dim.

Les sorties vidéo étant des panoramas/frames (large aspect ratio), le PNG downscalé à max-dim 1200 compresse efficacement — aucun fallback WebP nécessaire.

| Figure | Notebook source | Cellule | Output | Format | Dimensions | Poids | Alt-text FR |
|--------|-----------------|---------|--------|--------|------------|-------|-------------|
| `vid4-educational.png` | `04-1-Educational-Video-Generation.ipynb` | 9 | 2 | PNG | 1200×252 | 46,7 KB | Génération vidéo éducative — aperçu des frames |
| `vid4-creative.png` | `04-2-Creative-Video-Workflows.ipynb` | 9 | 2 | PNG | 1200×573 | 44,2 KB | Workflow créatif vidéo — séquence générée |
| `vid4-creative2.png` | `04-2-Creative-Video-Workflows.ipynb` | 15 | 2 | PNG | 1200×313 | 36,5 KB | Workflow créatif — variante de composition |
| `vid4-sora.png` | `04-3-Sora-API-Cloud-Video.ipynb` | 9 | 3 | PNG | 1200×422 | 48,4 KB | Simulation du workflow Sora (API cloud) |
| `vid4-sora2.png` | `04-3-Sora-API-Cloud-Video.ipynb` | 11 | 2 | PNG | 1200×200 | 35,7 KB | Simulation Sora — aperçu alternatif |
| `vid4-pipeline.png` | `04-4-Production-Video-Pipeline.ipynb` | 9 | 2 | PNG | 1200×236 | 73,2 KB | Pipeline vidéo production — orchestration |

**Diversité couverte** : 4 notebooks de cas d'usage production (Éducatif, Créatif, Sora API, Pipeline). Total : 6 figures, 284,7 KB, max 73,2 KB/fichier. Toutes PNG (frames vidéo compressibles, WebP non requis).

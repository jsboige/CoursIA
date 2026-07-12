# Manifeste des figures — Video 03-Orchestration

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Source native |
|--------|---------|------------|-------|--------------------------------------|---------------|
| Image source SDXL (pipeline text→image→vidéo) | `vid3-workflow1.webp` | 819×490 | 6 Ko | `03-2-Video-Workflow-Orchestration.ipynb` · cellule 8 · output 3 | 819×490, 10 Ko |
| Pipeline text→image→vidéo — planche-contact (source + frames 1-25) | `vid3-workflow2.webp` | 1200×201 | 8 Ko | `03-2-Video-Workflow-Orchestration.ipynb` · cellule 8 · output 10 | 1790×300, 113 Ko |
| Comparatif brut vs upscale + interpolation (LTX-Video, marguerite) | `vid3-frame1.webp` | 1200×531 | 40 Ko | `03-2-Video-Workflow-Orchestration.ipynb` · cellule 10 · output 9 | 1589×704, 984 Ko |
| Batch multi-prompts LTX-Video (océan / torche / montagnes, 3×4 frames) | `vid3-frame2.webp` | 1200×723 | 46 Ko | `03-2-Video-Workflow-Orchestration.ipynb` · cellule 12 · output 14 | 1389×837, 913 Ko |
| ComfyUI AnimateDiff — frames 1-8/16 (lac au couchant) | `vid3-comfyui.webp` | 1200×606 | 82 Ko | `03-3-ComfyUI-Video-Workflows.ipynb` · cellule 9 · output 4 | 1560×788, 1697 Ko |

**Total** : 5 figures, 185 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Les frames vidéo GenAI sont des images photographiques denses (sources 913–1697 Ko) : WebP q82 à 1200 px bat massivement le PNG (ex. frame 1 : 984 Ko → WebP 1200 px 40 Ko vs PNG 600 px 162 Ko — 2× la résolution pour 4× moins de poids). C'est la recommandation WebP P2 « quand le gain est net ».

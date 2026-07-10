# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

# Manifeste des figures — 03-Orchestration

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources re-exécutées en vrai (ComfyUI Qwen) le 2026-07-10 — #5867 (racine causale : bug de var-name `COMFYUI_AUTH_TOKEN` + timeout de poll trop court dans la cellule 9, corrigés).

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Source native |
|--------|---------|------------|-------|--------------------------------------|---------------|
| Grille multi-modèles | `img3-multimodel.webp` | 1182×596 | 67 Ko | `03-1-Multi-Model-Comparison.ipynb` · cellule 8 · output 2 | 1182×596, 542 Ko |
| Pipeline séquentiel | `img3-workflow1.webp` | 1200×411 | 32 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 11 · output 5 | 1500×500, 472 Ko (PNG) |
| Comparaison multi-modèles | `img3-workflow2.webp` | 1200×423 | 52 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 13 · output 2 | 1500×500, 513 Ko (PNG) |
| Pipeline conditionnel | `img3-workflow3.png` | 694×396 | 16 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 17 · output 5 | 800×400, 17 Ko (natif) |
| Générations multi-variations | `img3-workflow4.webp` | 1143×397 | 54 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 21 · output 4 | 1200×400, 524 Ko (PNG) |

**Total** : 5 figures, 224 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max, WebP fallback quand le gain est net. Les grilles de photos générées (séquentiel, comparaison, variations) compressent mal en PNG (472-524 Ko) — WebP q88 les ramène sous le plafond (32-54 Ko, ~10 % du PNG) sans perte visuelle sensible. Le pipeline conditionnel reste en PNG natif (diagramme en barres peu dense = 16 Ko).

## img3-workflow1.webp

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 11, output 5) — pipeline séquentiel (génération → style → upscaling)
- **Alt-text (FR)** : Pipeline séquentiel : image générée, puis stylée, puis suréchantillonnée
- **Poids** : 32 Ko (WebP q88, depuis PNG 472 Ko)

## img3-workflow2.webp

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 13, output 2) — comparaison multi-modèles en parallèle
- **Alt-text (FR)** : Comparaison parallèle de plusieurs modèles d'image sur un même prompt
- **Poids** : 52 Ko (WebP q88, depuis PNG 513 Ko)

## img3-workflow3.png

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 17, output 5) — pipeline conditionnel (score qualité vs tentatives)
- **Alt-text (FR)** : Diagramme en barres du score de qualité selon les tentatives d'un pipeline conditionnel
- **Poids** : 16 Ko (PNG natif)

## img3-workflow4.webp

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 21, output 4) — générations multi-variations par style
- **Alt-text (FR)** : Trois déclinaisons stylistiques d'un même prompt d'image
- **Poids** : 54 Ko (WebP q88, depuis PNG 524 Ko)

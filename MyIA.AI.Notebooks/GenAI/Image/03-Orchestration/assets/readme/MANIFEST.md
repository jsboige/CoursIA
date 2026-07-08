# Manifeste des figures — 03-Orchestration

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Source native |
|--------|---------|------------|-------|--------------------------------------|---------------|
| Grille multi-modèles | `img3-multimodel.webp` | 1182×596 | 67 Ko | `03-1-Multi-Model-Comparison.ipynb` · cellule 8 · output 2 | 1182×596, 542 Ko |
| Workflow — étape 1 | `img3-workflow1.png` | 1200×411 | 16 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 11 · output 5 | 1444×495, 13 Ko |
| Workflow — étape 2 | `img3-workflow2.png` | 1200×423 | 40 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 13 · output 2 | 1404×495, 23 Ko |
| Workflow — étape 3 | `img3-workflow3.png` | 694×396 | 16 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 17 · output 7 | 694×396, 17 Ko (natif) |
| Workflow — étape 4 | `img3-workflow4.png` | 1143×397 | 8 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 21 · output 2 | 1143×397, 9 Ko (natif) |

**Total** : 5 figures, 151 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max, WebP fallback quand le gain est net (ici la grille multi-modèles : WebP natif q88 = 67 Ko vs PNG 700 px = 193 Ko, 5,6× plus petit à pleine résolution). Les diagrammes de workflow (rendus vectoriels peu denses) restent en PNG natif.

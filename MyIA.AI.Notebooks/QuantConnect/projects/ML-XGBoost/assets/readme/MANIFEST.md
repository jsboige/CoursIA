# Manifeste des figures — ML-XGBoost

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet |
|--------|---------|------------|-------|---------------------------|-------|
| H1 — Learning rate | `xgb-h1-learningrate.png` | 1000×712 | 185 Ko | cellule 11 · output 4 | Learning rate (hypothèse 1) — downscale depuis 1389×989 |
| H2 — N estimateurs | `xgb-h2-nestimators.png` | 1389×989 | 197 Ko | cellule 14 · output 4 | Nombre d'estimateurs (hypothèse 2) |
| H3 — Seuil | `xgb-h3-threshold.png` | 1000×712 | 182 Ko | cellule 17 · output 4 | Seuil de prédiction (hypothèse 3) — downscale |
| H4 — Max positions | `xgb-h4-maxpositions.png` | 900×640 | 174 Ko | cellule 20 · output 4 | Nombre maximum de positions (hypothèse 4) — downscale |
| H5 — Subsample | `xgb-h5-subsample.png` | 1000×712 | 191 Ko | cellule 23 · output 4 | Subsample ratio (hypothèse 5) — downscale |
| Synthèse | `xgb-synthese.png` | 989×790 | 43 Ko | cellule 26 · output 0 | Importance des features |

**Total** : 6 figures, 974 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. H1/H3/H4/H5 (220–243 Ko natifs, denses) downscaled à 900–1000 px ; H2 passe natif après optimisation PNG (216 → 197 Ko). Arc : cinq hypothèses d'hyperparamètres XGBoost (learning rate, n estimateurs, seuil, max positions, subsample) → synthèse par importance des features.

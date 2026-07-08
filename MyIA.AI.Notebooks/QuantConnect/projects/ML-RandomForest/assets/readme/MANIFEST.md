# Manifeste des figures — ML-RandomForest

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet |
|--------|---------|------------|-------|---------------------------|-------|
| H1 — N estimateurs | `mrf-h1-nestimators.png` | 1000×712 | 197 Ko | cellule 11 · output 4 | Nombre d'estimateurs (hypothèse 1) — downscale depuis 1389×989 |
| H2 — Profondeur max | `mrf-h2-maxdepth.png` | 1389×989 | 192 Ko | cellule 14 · output 4 | Profondeur maximale des arbres (hypothèse 2) |
| H3 — Seuil | `mrf-h3-threshold.png` | 1000×712 | 196 Ko | cellule 17 · output 4 | Seuil de prédiction (hypothèse 3) — downscale depuis 1389×989 |
| H4 — Univers | `mrf-h4-universe.png` | 1389×989 | 190 Ko | cellule 20 · output 4 | Taille de l'univers d'actifs (hypothèse 4) |
| H5 — Fréquence train | `mrf-h5-trainfreq.png` | 1000×712 | 191 Ko | cellule 23 · output 4 | Fréquence d'entraînement (hypothèse 5) — downscale depuis 1389×989 |
| Synthèse | `mrf-synthese.png` | 989×590 | 29 Ko | cellule 26 · output 0 | Importance des features |

**Total** : 6 figures, 997 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Les figures H1/H3/H5 (207–233 Ko natifs, denses) sont downscaled à 1000×712 ; H2/H4 passent natifs après optimisation PNG (208/207 → 192/190 Ko). Arc : cinq hypothèses sur les hyperparamètres (n_estimators, max_depth, threshold, univers, fréquence d'entraînement) → synthèse par importance des features.

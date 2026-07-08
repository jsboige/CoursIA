# Manifeste des figures — ForexCarry

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet |
|--------|---------|------------|-------|---------------------------|-------|
| H1 — Momentum FX | `forex-h1-momentum.png` | 1156×500 | 58 Ko | cellule 5 · output 1 | Le momentum FX pur fonctionne-t-il (2018-2026) ? |
| H3 — Long-only vs L/S | `forex-h3-longshort.png` | 800×397 | 187 Ko | cellule 11 · output 0 | Long-only vs long/short (downscale depuis 1389×690) |
| H4 — 4 paires | `forex-h4-4pairs.png` | 800×397 | 170 Ko | cellule 14 · output 0 | Réduction à 4 paires (moins de corrélation) — downscale |
| H5 — Filtre DXY | `forex-h5-dxy.png` | 1389×690 | 163 Ko | cellule 17 · output 0 | Filtre DXY vs SPY SMA200 |
| H6 — Filtre volatilité | `forex-h6-vol.png` | 1389×690 | 163 Ko | cellule 20 · output 0 | Filtre de volatilité (régime) |
| Synthèse | `forex-synthese.png` | 1389×690 | 138 Ko | cellule 23 · output 0 | Meilleure configuration |

**Total** : 6 figures, 882 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. H3/H4 (240–274 Ko natifs, denses) sont downscaled à 800×397 ; H1/H5/H6/synthèse passent natifs. Arc : momentum FX (H1) → long-only vs L/S (H3) → réduction 4 paires (H4) → filtres DXY (H5) et volatilité/régime (H6) → configuration optimale.

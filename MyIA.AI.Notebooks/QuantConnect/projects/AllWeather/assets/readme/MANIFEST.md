# Manifeste des figures — AllWeather

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet |
|--------|---------|------------|-------|---------------------------|-------|
| Exploration | `aw-exploration.png` | 690×590 | 38 Ko | cellule 6 · output 1 | Rendements et volatilité annualisés par actif |
| H1 — Parity | `aw-h1-parity.png` | 1389×989 | 186 Ko | cellule 8 · output 1 | Static vs Risk Parity vs Tactical (equity curves) |
| H3 — Rebalancing | `aw-h3-rebalance.png` | 1389×989 | 113 Ko | cellule 14 · output 2 | Fréquence de rebalancement |
| H4 — SMA200 | `aw-h4-sma200.png` | 900×640 | 186 Ko | cellule 17 · output 2 | Overlay tactique SMA200 (downscale depuis 1389×989) |
| Comparaison | `aw-comparison.png` | 989×590 | 29 Ko | cellule 19 · output 0 | Sharpe et drawdown entre configurations testées |
| Grille optimale | `aw-grid-optimal.png` | 1390×490 | 127 Ko | cellule 24 · output 0 | Exploration de la grille de paramètres |

**Total** : 6 figures, 682 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Courbes matplotlib → **PNG lossless natif** (netteté des étiquettes). La figure H4 (257 Ko natif, dense) est downscaled à 900×640 pour rester sous le seuil (186 Ko). Arc : exploration des données → hypothèses H1 (parity) / H3 (rebalancing) / H4 (overlay SMA200) → comparaison des configurations → grille optimale.

# Manifeste des figures — EMA-Cross-Index

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet |
|--------|---------|------------|-------|---------------------------|-------|
| Grille EMA | `ema-grid-heatmap.png` | 1539×490 | 62 Ko | cellule 8 · output 0 | Heatmap du Sharpe ratio en fonction des périodes EMA (fast vs slow) |
| Backtest | `ema-backtest.png` | 1389×989 | 159 Ko | cellule 15 · output 0 | Courbe de rendement cumulatif & périodes de drawdown |
| H4 — Cooldown | `ema-h4-cooldown.png` | 1189×390 | 22 Ko | cellule 23 · output 3 | Cooldown après faux signal (hypothèse 4) |
| H5 — Trailing | `ema-h5-trailing.png` | 1389×989 | 149 Ko | cellule 26 · output 3 | Trailing stop vs sortie EMA (hypothèse 5) |
| Régime | `ema-regime.png` | 1389×1189 | 135 Ko | cellule 36 · output 1 | Classification des régimes (tendanciel / retour à la moyenne) |
| Filtre SMA200 | `ema-sma200-filter.png` | 1389×590 | 91 Ko | cellule 42 · output 1 | Sharpe & CAGR avec/sans filtre SPY SMA200 |

**Total** : 6 figures, 620 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Courbes matplotlib → **PNG lossless natif** (netteté des étiquettes ; tous sous le seuil sans downscale, max 159 Ko). Arc : grille de périodes EMA (recherche des 20/60) → backtest de référence → H4 cooldown / H5 trailing stop → régimes de marché → filtre SMA200.

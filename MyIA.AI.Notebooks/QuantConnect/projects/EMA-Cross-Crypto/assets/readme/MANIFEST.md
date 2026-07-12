# Manifeste des figures — EMA-Cross-Crypto

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet |
|--------|---------|------------|-------|---------------------------|-------|
| BTC + moyennes mobiles | `emacrypto-btc-emas.png` | 1389×690 | 140 Ko | cellule 11 · output 0 | Cours BTC et moyennes mobiles (EMA 20/60) |
| CAGR par configuration | `emacrypto-cagr.png` | 1583×590 | 129 Ko | cellule 19 · output 0 | Comparaison du CAGR entre configurations testées |
| Métriques | `emacrypto-metrics.png` | 1389×989 | 130 Ko | cellule 24 · output 0 | Comparaison Sharpe / CAGR / drawdown |
| Sharpe par configuration | `emacrypto-sharpe.png` | 1589×690 | 148 Ko | cellule 32 · output 0 | Comparaison du Sharpe entre configurations |
| Drawdowns | `emacrypto-drawdowns.png` | 1389×989 | 137 Ko | cellule 34 · output 1 | Analyse des drawdowns par période (§9) |

**Total** : 5 figures, 686 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Courbes matplotlib → **PNG lossless natif** (netteté des étiquettes ; tous sous le seuil sans downscale, max 148 Ko). Arc : cours BTC + moyennes mobiles → comparaison des configurations (CAGR, Sharpe/drawdown) → analyse des drawdowns par période.

# Manifeste des figures — DualMomentum

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet |
|--------|---------|------------|-------|---------------------------|-------|
| Exploration | `dm-exploration.png` | 1590×590 | 122 Ko | cellule 4 · output 1 | Analyse exploratoire (§2) |
| Drawdown | `dm-drawdown.png` | 1589×1389 | 170 Ko | cellule 14 · output 0 | Comparaison des drawdowns entre configurations |
| H2 — Lookback | `dm-h2-lookback.png` | 1389×490 | 23 Ko | cellule 16 · output 1 | Robustesse par lookback period (hypothèse 2) |
| Sharpe | `dm-sharpe.png` | 1389×490 | 76 Ko | cellule 21 · output 1 | Comparaison du Sharpe entre configurations |

**Total** : 4 figures, 392 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Courbes matplotlib → **PNG lossless natif** (tous sous le seuil sans downscale, max 170 Ko). Arc : exploration → comparaison des drawdowns → robustesse au lookback (H2) → comparaison du Sharpe. Stratégie documentée comme remplacée par DualMomentumNoTLT (contre-exemple pédagogique, échec TLT 2022).

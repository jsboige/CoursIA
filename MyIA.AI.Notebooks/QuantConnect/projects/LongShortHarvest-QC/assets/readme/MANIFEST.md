# Manifeste des figures — LongShortHarvest-QC

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet |
|--------|---------|------------|-------|---------------------------|-------|
| Backtest de référence | `lsh-reference.png` | 1189×790 | 102 Ko | cellule 9 · output 1 | Cours SPY/GLD/VIX et backtest de référence |
| Sweep H1 — score_threshold | `lsh-h1-sweep.png` | 1390×490 | 27 Ko | cellule 11 · output 1 | Sensibilité au seuil de score |
| Equity curves H1 | `lsh-h1-equity.png` | 1189×490 | 39 Ko | cellule 12 · output 0 | Courbes de capital par seuil |
| Equity curves H2 | `lsh-h2-equity.png` | 1189×490 | 41 Ko | cellule 15 · output 0 | Courbes de capital par ext_k |
| Walk-forward | `lsh-walkforward.png` | 1389×590 | 60 Ko | cellule 25 · output 0 | Rendements walk-forward par fenêtre |
| Régime | `lsh-regime.png` | 1590×490 | 25 Ko | cellule 27 · output 1 | Performance par régime de marché |

**Total** : 6 figures, 302 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Courbes matplotlib → **PNG lossless natif** (netteté des étiquettes ; plots 25–113 Ko natifs, sous le seuil sans downscale). Arc : backtest de référence → sensibilité aux hyperparamètres (H1/H2) → validation walk-forward → performance par régime.

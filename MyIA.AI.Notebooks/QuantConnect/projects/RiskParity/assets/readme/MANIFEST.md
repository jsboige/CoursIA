# Manifeste des figures — RiskParity

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet |
|--------|---------|------------|-------|---------------------------|-------|
| Exploration | `rp-exploration.png` | 1544×487 | 114 Ko | cellule 4 · output 1 | Analyse exploratoire des actifs (§2) |
| H1 — Inverse-vol | `rp-h1-inversevol.png` | 1787×493 | 34 Ko | cellule 6 · output 1 | Inverse-volatility weighting égalise les contributions (H1) |
| H2 — Backtest | `rp-h2-backtest.png` | 1586×986 | 166 Ko | cellule 8 · output 1 | Simulation du backtest risk parity (H2) |
| H3 — Impact TLT | `rp-h3-tlt.png` | 800×495 | 187 Ko | cellule 12 · output 0 | Impact de TLT en 2020-2023 (hausse des taux, H3) — downscale depuis 1587×983 |
| H4 — Lookback | `rp-h4-lookback.png` | 1387×487 | 34 Ko | cellule 14 · output 1 | Sensibilité au lookback de volatilité (H4) |
| Régime | `rp-regime.png` | 1387×587 | 36 Ko | cellule 16 · output 2 | Analyse par régime de marché (§7) |

**Total** : 6 figures, 573 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. H3 (297 Ko natif, dense) downscaled à 800×495 ; les autres passent natifs (34–166 Ko). Arc : exploration → H1 inverse-vol (égalisation des contributions) → H2 backtest risk parity → H3 impact TLT 2020-2023 → H4 sensibilité au lookback → analyse par régime. Stratégie documentée comme plafond structurel (Sharpe 0.399, contre-exemple pédagogique).

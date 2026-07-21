# ARCHIVE - BTC-ML (ML Crypto via RandomForestClassifier)

**Status** : ARCHIVED (substance pédagogique préservée)
**Date d'archive** : 2026-07-21
**Sharpe OOS** : 0.057 (NO BEATS, edge statistiquement indistinguable du bruit)
**Issue de reference** : #7575 (bug-class `PREEXISTING_UNEXEC` quantbooks sans `config.json`)

## Strategy Summary

Stratégie de machine learning sur Bitcoin (BTCUSDT, Binance) utilisant
`sklearn.ensemble.RandomForestClassifier` (n_estimators=50, max_depth=4,
min_samples_leaf=10) sur des features trend/momentum classiques (SMA, RSI,
EMA 10/20/50/200, ADX, ATR, volatilité annualisée).

Construction de features en walk-forward strict, ré-entraînement périodique
(intervalle 60 jours, lookback 2 ans), position sizing probabiliste
(confidence thresholds), filtre de volatilité, et risk management
(stop-loss -8 %, take-profit +15 %).

Split train/OOS strict : training 2017-2020, out-of-sample backtest
2021-2026 (5 ans, aucun recouvrement).

## Backtest Metrics (OOS vérifié)

| Metric | Value |
|--------|-------|
| Méthode | RandomForestClassifier (n=50, depth=4, leaf=10) |
| Univers | BTCUSDT (Binance, daily) |
| Rebalance | Daily |
| Sharpe ratio | 0.057 |
| Probabilistic Sharpe | 1.520 % |
| CAGR | 3.692 % |
| Max drawdown | 15.400 % |
| Total net profit | +20.612 % (USDT 20,612 sur 100k) |
| Total orders | 13 |
| Tradeable days | 1886 |

## Iteration History

| Version | Modification | Sharpe | Verdict |
|---------|--------------|--------|---------|
| v1.0 | RF basique (n=100, depth=8) | N/A | Baseline |
| v2.0 | + walk-forward strict + retraining 60j | N/A | Improved scaffolding |
| v3.0 | + position sizing probabiliste + risk mgmt | 0.057 | **NO BEATS** vs buy-and-hold BTC sur OOS |

## Verdict

Le **Sharpe 0.057** et le **Probabilistic Sharpe 1.520 %** indiquent que
l'edge de la stratégie sur cette fenêtre OOS est statistiquement
indistinguable du bruit. **NO BEATS** vs buy-and-hold BTC sur la même
période (2021-2026).

Verdict honnête : la stratégie s'exécute proprement (BuildSuccess, 0
erreur de compilation, pas de data leakage), mais **ne démontre pas
d'alpha**. À conserver comme **référence pédagogique** pour le
scaffolding ML-stratégie (séparation train/OOS, walk-forward, retraining
périodique, position sizing probabiliste) — **pas comme source d'alpha
live**.

## Notes d'infrastructure

- **QC Cloud** : déployé (projet 29318876 selon README). Le `config.json`
  est absent du repo, mais le README atteste du `cloud-id` et d'un
  backtest vérifié (po2026-verify-btc-ml-oos-2021-2026, 2026-07-15,
  BuildSuccess, 0 erreur compile).
- **`config.json` manquant** : incohérence documentée (G.1) entre la
  prose README (cloud-id présent) et le disk (config absent). À noter
  pour un futur sweep de cohérence QC Cloud.
- **quantbook.ipynb** : 8/11 cellules non-exécutées (`execution_count:
  null`, `outputs: []`) — substance pédagogique préservée dans
  `main.py` + `README.md` + `research.ipynb` (300 KB, fully executed).

## Leçons retenues

1. **Le scaffolding ML n'est pas l'alpha** : walk-forward, retraining
   périodique, position sizing probabiliste sont des bonnes pratiques,
   mais ne suffisent pas à garantir un edge — surtout sur crypto où le
   buy-and-hold domine structurellement les fenêtres 2021-2026.
2. **Sharpe OOS vs buy-and-hold** : benchmark obligatoire pour les
   stratégies directionnelles sur actif trend-following. Un Sharpe
   absolu de 0.057 peut être honnête mais inutile.
3. **Le sharpe ratio probabiliste** (PS) est plus informatif que le
   Sharpe seul : 1.52 % indique que l'edge est dominé par le bruit
   d'estimation, pas par un vrai signal.
4. **Le dépot QC Cloud sans `config.json`** : la procédure de
   cohérence disk↔prose est faible. À renforcer dans un futur sweep.

## Fichiers

- `main.py` (16 KB) — Stratégie `MyEnhancedCryptoMlAlgorithm`
- `research.ipynb` (300 KB) — Recherche exécutée localement
- `quantbook.ipynb` (27 KB) — Exploration QuantBook (8/11 cells unexec)
- `README.md` — Description, métriques, verdict

## References

- #7575 (issue parent) — bug-class `PREEXISTING_UNEXEC` quantbooks
- #6891 (sibling) — fabrication degeneration body, distinct bug-class
- `scripts/quantconnect/audit_quantbooks_unexec.py` — détecteur
- `.claude/rules/sota-not-workaround.md` — Prong-A vrai outil, pas
  workaround/fabrication

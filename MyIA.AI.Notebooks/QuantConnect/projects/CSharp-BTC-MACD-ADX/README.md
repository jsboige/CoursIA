# BTC MACD + ADX Adaptive (C#) (ID: 30751067)

Stratégie momentum BTCUSDT combinant MACD (tendance) et ADX (force) avec seuils adaptatifs par percentile (implémentation C#).

## Performance (lecture vérifiée frais réels — NO-BEATS)

Backtest frais Binance réels, 2019-04-01 → 2026-08 (2684 jours tradeables, 52 ordres), projet de vérification Cloud `CSharp-BTC-MACD-ADX-verify` (34901074) :

| Métrique | Valeur vérifiée (frais réels) | Catalogue (pré-frais) |
|----------|-------------------------------|----------------------|
| **Sharpe** | **0.123** | 0.787 |
| **CAGR** | **0.037 %** (quasi-plat sur 7 ans) | — |
| **Max Drawdown** | **72.7 %** | — |
| **Profit net** | **0.274 %** | — |
| **PSR** | **0.814 %** (bruit, seuil 95 %) | — |

**Verdict : NO-BEATS.** Le Sharpe 0.123 — avec un PSR de 0.8 %, statistiquement indissociable du bruit — confirme l'effondrement pré-frais → frais réels déjà documenté pour la famille (See #1630) : le catalogue 0.787 (pré-frais, fenêtre variable) tombe à 0.123 sur la fenêtre alignée 7 ans avec frais Binance réels. La stratégie sous-performe massivement le buy & hold BTC (~500 %+ sur la même période) avec un drawdown catastrophique de 72.7 %.

Ce verdict corrobore [`RESEARCH_FINDINGS.md`](RESEARCH_FINDINGS.md) (2026-02-17) : l'approche adaptative à seuils percentile ne tient pas ses promesses — toutes les hypothèses H1-H5 rejetées, Sharpe -0.035 pour les paramètres originaux (Window=140). Les paramètres optimisés actuels (`Main.cs` : Window=40, percentiles 10/90) n'inversent pas la conclusion : 0.123 reste non robuste.

## Stratégie

- **MACD** : direction et momentum de tendance (fast 12 / slow 26 / signal 9, EMA)
- **ADX** : filtre de force de tendance (période 25) pour éviter les marchés sans direction
- **Seuils adaptatifs** : entrée long si ADX ≥ percentile 90 ET MACD haussier ; sortie si ADX < percentile 10 ET MACD baissier (fenêtre glissante 40 jours)
- **Univers / brokerage** : BTCUSDT daily, Binance compte Cash, capital 5000 USDT

## Fichiers

| Fichier | Description |
|---------|-------------|
| `Main.cs` | Implémentation C# (paramètres optimisés Window=40, percentiles 10/90) |
| `Research.ipynb` | Notebook de recherche principal |
| `research_robustness.ipynb` | Analyse de robustesse (grid search 2019-2025) |
| `RESEARCH_FINDINGS.md` | Conclusions de recherche (hypothèses H1-H5 rejetées) |
| `RESEARCH_SUMMARY.md` | Résumé exécutif |

## Source

partner-course-quant-trading/examples/CSharp-BTC-MACD-ADX (archivé après standardisation).

---

*Performance vérifiée sous frais réels sur fenêtre alignée 2019-2026 (See #1621 Phase 4 / #1630). Le catalogue pré-frais (Sharpe 0.787) surestime la stratégie ; la lecture alignée (Sharpe 0.123, PSR 0.8 %, MaxDD 72.7 %) est non robuste et ne bat pas le buy & hold. Version anglaise préservée dans [`README.en.md`](README.en.md).*

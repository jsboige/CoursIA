# Migration Plan : M12 HAR-RV-J + M11ef Ensemble → QuantBook + Algo backtested QC Cloud

**Date** : 2026-05-13
**Author** : ai-01 (research side-track B, post user A.3 directive)
**Goal** : promouvoir nos 2 modèles BEATS validés (M12 HAR-RV-J single-asset + M11ef ensemble long-horizon fee-robust) de scripts Python locaux vers **QuantBook research notebooks + algorithmes backtestés sur QC Cloud**, en préparation de mise en œuvre dans l'infra QC Cloud (Phase 1 Portfolio Hybride paper-trading → live nodes).

## Pourquoi maintenant (user A.3 directive)

Citation user 13/05 ~20:30Z : *"Il faut continuer à itérer sur les bases de nos échecs, de leçons du livre et des publication SOTA et selon la qualité des données disponibles et nos possibilités de training. Il faut aussi voir pour passer nos bons modèles à l'épreuve de QC (QuantBook + algos backtestés, voir ce que ça implique pour une mise en oeuvre dans l'infra de cloud QC)."*

Le verdict M-series cumulé indique seul **M12 HAR-RV-J cluster BEATS** (sign-test p=7.9e-7, 64/84 wins, delta-Sharpe +0.0032 vs HAR Classic baseline) et **M11ef** ensemble long-horizon fee-robust à 50bps (PR #987, sign-test p=0.045 K60 vs BH, survit jusqu'à ~100bps). Ces 2 modèles méritent l'épreuve cloud QC avant ESGF 19/05.

## État actuel

| Modèle | Script local | Walk-forward | Multi-seed | Verdict | QuantBook | Algo QC | Backtest QC |
|--------|--------------|--------------|------------|---------|-----------|---------|-------------|
| **M12 HAR-RV-J** | `scripts/m12_har_rv_jumps.py` | 5-fold | 4 (deterministic OLS) | **BEATS** p=7.9e-7 | ❌ | ❌ | ❌ |
| **M11ef ensemble** | `scripts/m11e_ensemble.py` + `m11f_fee_aware.py` | 5-fold | 4 | **BEATS** K60-vs-BH p=0.045 @50bps | ❌ | partiel (sleeve EMA-Cross-Crypto existant) | ❌ |

Aucun des 2 n'a vu QC Cloud. Tous les BEATS rapportés sont sur données G drive locales (10 ans Bitstamp BTC + 4y altcoins).

## Implications QC Cloud (livre Broad *Hands-On AI Trading*)

### Pour M12 HAR-RV-J

1. **Data source** : QC fournit crypto OHLCV horaire via `QuantBook().Crypto("BTCUSD", Resolution.Hour, Market.Bitstamp)` ou équivalent Coinbase. Period start 2018-01-01 OK pour BTC, ~2020 pour altcoins.
2. **Realized variance reconstruction** : HAR utilise RV journalière calculée depuis returns intraday. QC Hour-resolution = 24 returns/jour → reconstruct RV via `np.sum(log_returns**2)` sur fenêtre quotidienne. Vérifier alignement avec G drive Bitstamp Tick.
3. **Jump detection** (Huang-Tauchen bipower variation) : pure pandas/numpy, portable.
4. **Backtest algo** : implementation `Initialize/OnData` standard. HAR coefficients refittés rolling (window 252 jours) ou static post training set. Position sizing = Kelly threshold-band selon vol forecast.
5. **Transaction costs** : QC simule fees Coinbase/Binance natif (typically 10bps maker / 25bps taker). M11ef l'a déjà documenté.
6. **Walk-forward Cloud** : QC backtest est single-period par défaut. Walk-forward = N backtests séquentiels via `BacktestingResultHandler` (cf livre Broad Ch07-08). Possibilité de scripter via MCP qc-mcp `create_backtest` × N folds.

### Pour M11ef ensemble

1. **Composantes** : K60 (Kelly cap=0.6) + K30 + VTH. Chaque sleeve = strat existante ou nouvelle.
2. **Backtest natif QC** :
   - K60 / K30 = Kelly threshold-band sur HAR ou EMA cross. Adaptable.
   - VTH = vol-targeting via QC `RiskManagementModel` natif.
   - Rebalance mensuel = `Schedule.On(DateRules.MonthStart(), TimeRules.AfterMarketOpen("SPY", 30))`.
3. **Fee robustness** : QC simule fees natif. Slippage Bitstamp/Binance peut être custom override.
4. **Verdict survival check** : reproduire BEATS @50bps via QC backtest matching local Python sweep (3 sleeves × 4 horizons × 4 seeds).

## Migration roadmap (3 phases)

### Phase A — QuantBook research notebooks (4-6 jours)

Cible : pour chaque modèle, créer 1 QuantBook research notebook qui reproduit le verdict local.

| Notebook | Domaine | Sections obligatoires |
|----------|---------|----------------------|
| `MyIA.AI.Notebooks/QuantConnect/research_M12_HAR_RV_J/research_har_rv_j.ipynb` | M12 single-asset | (1) data load via QB, (2) RV reconstruction, (3) HAR-RV-J fit walk-forward, (4) DM test vs HAR Classic, (5) Kelly sizing backtest, (6) verdict matrix coin × horizon |
| `MyIA.AI.Notebooks/QuantConnect/research_M11ef_Ensemble/research_ensemble.ipynb` | M11ef multi-sleeve | (1) data load 4 majors crypto, (2) K60/K30/VTH sleeve backtest individuel, (3) ensemble equal-weight, (4) fee sweep [0, 5, 10, 25, 50, 100 bps], (5) DM test vs BH, (6) verdict fee-robust horizon × cost |

**Discipline** :
- QuantBook = exécution **via QC Cloud** (MCP qc-mcp ou Playwright fallback)
- Outputs réels QC Cloud commités (règle C.2)
- Anti-FAANG : crypto only, no equity stock-picking single-name
- Multi-seed conservé (4 seeds 0/7/42/99) même pour HAR (deterministic) pour exhaustivité protocole

### Phase B — Algorithms QC + backtests (3-5 jours)

Pour chaque modèle ayant produit un BEATS en Phase A : `main.py` algo deployable + backtest QC Cloud.

| Algo | Path | Universe | Backtest period |
|------|------|----------|----------------|
| `HarRvJSingleAsset` | `MyIA.AI.Notebooks/QuantConnect/projects/M12-HAR-RV-J-BTC/` | BTC/USD | 2018-01-01 → 2025-12-31, OOS 2024-2025 |
| `Ensemble M11ef` | `MyIA.AI.Notebooks/QuantConnect/projects/M11ef-Crypto-Ensemble/` | BTC/ETH/LTC/SOL | 2020-01-01 → 2025-12-31, OOS 2024-2025 |

**Critères de sortie** :
- Compile OK (`create_compile`)
- Backtest run OK (`create_backtest`)
- Métriques Sharpe/CAGR/MaxDD reportées
- OOS distinct training set (anti-leak)
- Reporter dans body PR + dashboard `[INFO]`

### Phase C — Intégration Portfolio Hybride (1-2 cycles)

Si M12-BTC backtest QC ≥ Sharpe 1.0 et M11ef-Ensemble Sharpe ≥ 0.8 fee-robust, intégrer :

- M12-BTC dans Binance sleeve Portfolio Hybride (PR #1029) avec poids dynamique vol-target
- M11ef-Ensemble dans Binance sleeve comme alternative au mix EMA-Cross-Crypto + Crypto-MultiCanal + HAR-RV-J

Phase 1 Portfolio Hybride (po-2026 dispatched 16:37Z) puis backtest combiné sur QC Cloud.

## Implications infrastructure QC Cloud

### Free vs Paid resources

QC docs confirment :
- **Backtest** : gratuit pour subscribers (8h compute/mois free tier, illimité pour QCCC subscribers)
- **Alternative data Tiingo News / Brain Sentiment** : **gratuit** pour backtesting + Alpha Streams (cf [QC alternative data docs](https://www.quantconnect.com/docs/v2/cloud-platform/datasets/quantconnect/alternative-data))
- **Live trading nodes** : payant (~$50-500/mois selon tier, cf docs)
- **Premium datasets** : payant (Extract Alpha $75-450/mois, Quiver $5-15/mois, Benzinga $120/mois). **Pas nécessaire pour M12/M11ef** (HAR + EMA = OHLCV uniquement).

### Conclusion budget Phase A+B

**0 QCCC nécessaire**. M12 et M11ef tournent sur OHLCV gratuit. Plan Phase 1 Tiingo News 5k QCCC posté Epic #1027 est à **retracter** (data already free for backtest). Live trading nodes en Phase C+ uniquement.

### Rate limits QC API

- `create_backtest` : limité, cf docs
- MCP qc-mcp : MAX 10 appels/min entre tous agents (rule CLAUDE.md QC section)
- Annoncer sur dashboard avant batch backtest

## Risques connus

1. **RV reconstruction mismatch** : si QC Hour-resolution returns ≠ G drive Bitstamp Tick aggregé, M12 verdict QC peut différer. Audit en début Phase A.
2. **Slippage QC default** : peut être conservateur vs réel Binance maker. Documenter dans verdict.
3. **Crypto coverage QC** : altcoins SOL/DOT peuvent avoir data plus courte que G drive (Bitstamp 2017-2025 vs QC depends on exchange added).
4. **Walk-forward cost** : N=5 folds × 7 coins × 3 horizons = 105 backtests par modèle. Compute budget à vérifier (Free 8h/mois insuffisant probablement).

## Dispatch

| Phase | Agent | Quand | ETA |
|-------|-------|-------|-----|
| A.1 M12 QuantBook | po-2024 ou po-2025 | post-Cycle 34 (après M17 verdict ou ALPHA batch 1) | 2-3 jours |
| A.2 M11ef QuantBook | po-2024 ou po-2025 | parallel A.1 ou suivant | 2-3 jours |
| B.1 M12 algo + backtest | po-2024 | post-A.1 BEATS confirmé | 1-2 jours |
| B.2 M11ef algo + backtest | po-2024 | post-A.2 BEATS confirmé | 2-3 jours |
| C Portfolio Hybride intégration | po-2026 | post-Phase 1 Portfolio Hybride OK | 1 cycle |

## Acceptance criteria globale

- 2 QuantBook research notebooks committed avec outputs QC Cloud réels
- 2 algos `main.py` deployables avec backtest QC Cloud success
- Verdict matrix par modèle (Sharpe/CAGR/MaxDD/Calmar/Beta vs BH)
- Comparaison local Python vs QC Cloud (mismatch < 5% accepté, sinon audit)
- Phase 1 Portfolio Hybride intégration documentée
- Total budget : 0 QCCC (gratuit pour backtest)

## Références

- Broad J. (2025), *Hands-On AI Trading*, Ch04 Dataset Prep, Ch07 RL Options, Ch08 Corrective AI, Ch10 Alternative Data, Ch11 Macro Overlay
- [QC Alternative Data docs](https://www.quantconnect.com/docs/v2/cloud-platform/datasets/quantconnect/alternative-data)
- [QC Algorithm Lab guide](https://www.quantconnect.com/docs/v2/cloud-platform/projects)
- Andersen T.G., Bollerslev T., Diebold F.X. (2007), "Roughing It Up" (RV jumps / continuous-discontinuous decomposition)
- Hansen P.R. (2012), "Realized GARCH" (M10 baseline, NO BEATS, mais infrastructure RV utilisable)

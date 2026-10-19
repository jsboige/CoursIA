# composite-c1-multiasset

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** N/A

## Description

Composite C4.1 de rotation multi-actifs (v10), construit sur l'Alpha Framework. Cinq ETF (SPY, TLT, GLD, USO, EFA), levier 2x. Trois modèles d'alpha : MomentumAlpha (suivi de tendance), MACDAlpha (croisement MACD / ligne de signal) et RelativeStrengthAlpha (force relative entre classes d'actifs). Construction du portefeuille par poches : chaque alpha reçoit un tiers du capital via `MultiStrategyPouchesPCM` du module partagé `SharedPCM`, avec un rebalancement hebdomadaire et un plafond de 40 % par ligne. Une poche dont l'alpha n'a aucun insight actif reste en liquidités. Gestion du risque : plafond de baisse de 12 % et stop suiveur de 4 %. Exécution VWAP (4 tranches, fenêtre de 15 minutes).

Deux paramètres de projet servent aux comparaisons : `pcm_mode` (`sleeve` par défaut, `symbol` pour reprendre `RiskParityPCM`, le PCM d'avant) et `alphas` (`all` par défaut, ou `momentum`, `macd`, `relstrength` pour isoler un alpha).

## How to Run

### Lean CLI
```bash
lean backtest --algorithm composite-c1-multiasset/main.py
```

### QC Cloud
Create a new project, upload all `.py` files, compile and run a backtest.

Le projet importe `SharedPCM.pouches_pcm` : attacher d'abord le projet `SharedPCM` comme bibliothèque (voir `../SharedPCM/README.md`), sinon la compilation échoue sur l'import.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Alpha Framework (3 alphas, une poche d'un tiers par alpha) | Hebdomadaire | Levier 2x, plafond de baisse 12 %, stop suiveur 4 %, exécution VWAP en 4 tranches |

### Aligned baseline (2018-2025)

Standardized #1630 backbone run (QC Cloud project `32981093`, backtest `1236cf59`).

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.258 |
| CAGR | 6.490% |
| Max Drawdown | 17.000% |
| Probabilistic Sharpe Ratio | 8.7% |
| Tradeable dates | 1761 |

Interpretation: weak positive Sharpe 0.258 (comparable to the simple momentum rotations AssetClassMomentum 0.22 and Vol-Ensemble-Conservative 0.265). The 3-alpha ensemble (Momentum + MACD + RelativeStrength) combined with the RiskParityPCM (weekly, 100% exposure, 40% sector cap), 12% drawdown cap + 4% trailing stop, and VWAP execution adds little over a single momentum signal on the aligned period -- the composite architecture does not dramatically beat its components. MaxDD is controlled at 17% by the drawdown cap (vs 22.8% for the uncapped GlobalMacro-Regime). Far below the framework composite leaders FamaFrenchAllWeather (0.684) and EMATrend (0.741): COMP composites vary widely (c1 weak vs AllWeather/EMATrend strong), so the component alpha/PCM choice matters more than the framework wiring itself. Notably the aligned Sharpe 0.258 is higher than the catalog-campaign figure (0.175), so alignment did not degrade this composite. PSR 8.7% non-significant. Promoted Tier 4 -> 2 (Historique). totalOrders = 0 = wrapper extraction artifact (CAGR 6.49% implies real trades).

Cette lecture est à reprendre : la mesure #21147 ci-dessous montre que ce composite ne combinait pas trois alphas. Momentum n'atteignait jamais le PCM, et le résultat est celui de MACD seul.

### Mesure #21147 : un alpha par poche (2018-2025)

Lean ne transmet au PCM que le dernier insight actif par symbole (mécanisme de #19740). Les trois alphas visent les cinq mêmes ETF : `RiskParityPCM` ne voyait donc qu'un alpha par ligne. `Momentum` et `RelStrength` émettent au premier jour de bourse du mois (insights de 31 jours), `MACD` chaque semaine (7 jours).

Fenêtre du 2018-01-01 au 2025-01-01, fin non tronquée, mêmes fichiers et mêmes paramètres de stratégie pour toutes les variantes (aucun ajustement sur données). Un seul passage sur la fenêtre, sans validation glissante.

| Variante | `pcm_mode` | `alphas` | Sharpe | CAGR | Pire baisse | PSR | Ordres |
|---|---|---|---|---|---|---|---|
| A. Code d'avant | `symbol` | `all` | 0,261 | 6,49 % | 17,0 % | 0,87 % | 3692 |
| B1. Momentum seul | `symbol` | `momentum` | 0,080 | 4,30 % | 16,3 % | 0,16 % | 1498 |
| B2. MACD seul | `symbol` | `macd` | 0,263 | 6,52 % | 17,4 % | 0,89 % | 3339 |
| B3. RelStrength seul | `symbol` | `relstrength` | -0,005 | 3,30 % | 13,0 % | 0,07 % | 1556 |
| C. Une poche par alpha | `sleeve` | `all` | 0,167 | 5,39 % | 17,8 % | 0,38 % | 3640 |

Insights par alpha (actifs / reçus), relevés en statistiques runtime sur les 821 appels du PCM :

| Alpha | A : transmis par Lean au PCM | C : vus par la reconstruction par poches |
|---|---|---|
| Momentum | 0 / 0 | 2055 / 4105 |
| MACD | 1964 / 3390 | 2400 / 4105 |
| RelStrength | 261 / 715 | 1495 / 4105 |

Lecture :

- A reproduit la mesure historique (CAGR 6,49 %, pire baisse 17,0 %). Momentum n'atteint jamais le PCM. MACD, émis chaque semaine, porte 3390 des 4105 insights reçus ; RelStrength ne passe qu'au début du mois. En pratique, le composite d'avant est MACD seul : Sharpe 0,261 contre 0,263.
- C fait entrer les trois alphas : la reconstruction voit 4105 insights pour chacun, cinq symboles par appel. Verdict **NO BEATS** : Sharpe 0,167 contre 0,261 pour A et 0,263 pour MACD seul, avec une pire baisse un peu plus forte (17,8 %).
- Les deux alphas mensuels sont faibles sur la période (Sharpe 0,080 et -0,005). Leur donner deux tiers du capital dilue le seul alpha qui porte le résultat. Sur cet univers, l'élément à garder en concurrence est MACD hebdomadaire, pas l'assemblage à trois alphas.

## Files

| File | Description |
|------|-------------|
| `main.py` | Composite algorithm orchestrating alpha models, PCM, risk management, and execution |
| `alpha_models.py` | Three alpha models: Momentum, MACD, and Relative Strength |
| `portfolio_construction.py` | `CappedPouchesPCM` (mode `sleeve` : PCM par poches de `SharedPCM`, plafond par ligne) et `RiskParityPCM` (mode `symbol`, PCM d'avant), avec les compteurs d'insights par alpha |
| `risk_management.py` | Drawdown cap (12%) and trailing stop (4%) risk models |
| `execution.py` | VWAP execution model (4 slices, 15-minute window) |

## References

- [QuantConnect Alpha Framework](https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework)
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)

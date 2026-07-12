# Framework Composite - MomentumSector + RegimeSwitching

## Description

Stratégie composite combinant deux approches complémentaires via le QuantConnect Algorithm Framework :

1. **SectorMomentum (tranche 60 %)** : Dual momentum entre SPY/IEF/GLD
   - Score composite multi-lookback (1/3/6/12 mois)
   - Filtre SMA200 sur SPY
   - Rééquilibrage mensuel

2. **RegimeSwitching (tranche 40 %)** : Stratégie dépendante du régime
   - Marchés haussiers : Momentum ajusté du risque sur SPY/QQQ (70/30)
   - Marchés baissiers/latéraux : Mean-reversion (RSI survendu) + défensif (GLD/IEF)
   - Détection de régime via SMA50/SMA200 sur SPY

## Fichiers

- `main.py` : Configuration de l'algorithme avec CompositeAlpha et MultiStrategyPCM
- `alpha_models.py` : Classes SectorMomentumAlpha et RegimeSwitchingAlpha
- `portfolio_construction.py` : MultiStrategyPCM pour l'allocation de capital par stratégie

## Résultats de backtest (T60/RS40)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.185 |
| CAGR | 4.728 % |
| Net Profit | 66.272 % |
| Max Drawdown | 11.500 % |
| Total Orders | 520 |
| Win Rate | 73 % |
| Alpha | -0.008 |
| Beta | 0.218 |
| Sortino | 0.196 |

**Verdict** : Sous-performance. Le Sharpe 0.185 est bien en dessous de SectorMomentum
autonome (0.555). La composante RegimeSwitching dilue les rendements dans le blend 60/40.
Le beta très faible (0.218) indique que le composite est trop conservateur.

**Prochaines étapes** : Tester T80/RS20 ou T90/RS10 pour réduire la traînée du
RegimeSwitching, ou remplacer RegimeSwitching par une variante plus agressive bull-only.

## Cloud IDs

- Project ID : 31243821
- Organization : d600793ee4caecb03441a09fc2d00f7f

## Période de backtest

2015-01-01 à 2025-12-31

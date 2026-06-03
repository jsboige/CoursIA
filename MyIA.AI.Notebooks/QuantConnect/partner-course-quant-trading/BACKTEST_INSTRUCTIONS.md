# Instructions Backtests QuantConnect

## Stratégies à Backtester

### 1. BTC-MACD-ADX (OPTIMISÉ - MACD+ADX conservé)
- **URL** : https://www.quantconnect.com/project/19898232
- **Nom backtest** : `Optimized-MACD-ADX-Window80-Pct5-85`
- **Optimisation** : Window 140→80, Percentiles 6/86→5/85
- **Sharpe attendu** : +0.35 (vs -0.035 avant)

### 2. ETF-Pairs-Trading
- **URL** : https://www.quantconnect.com/project/19865767
- **Nom backtest** : `Optimized-HalfLife-Filter`
- **Optimisation** : HL filter <30j, duration adaptive, stops désactivés
- **Sharpe attendu** : 0.3-0.7 (vs -0.759)

### 3. Sector-Momentum
- **URL** : https://www.quantconnect.com/project/20216980
- **Nom backtest** : `Optimized-VIX-Filter`
- **Optimisation** : VIX filter >25, leverage 1.5x
- **Sharpe attendu** : 0.8-1.0+ (vs 0.5-0.8 sans VIX)

## Instructions

1. Ouvrir le projet via l'URL
2. Cliquer "Backtest" dans le menu
3. Cliquer "New Backtest"
4. Attendre la completion (5-15 min)
5. Noter: Sharpe, Total Return, Max DD

## Comparaison aux Prédictions

Après chaque backtest, comparer:

| Stratégie | Sharpe Attendu | Sharpe Réel | Écart | Validation |
|-----------|----------------|------------|-------|------------|
| BTC-MACD-ADX | > 0.35 | ___ | ___ | ✅ si >0.15 |
| ETF-Pairs | 0.3-0.7 | ___ | ___ | ✅ si >0.2 |
| Sector-Momentum | 0.8-1.0 | ___ | ___ | ✅ si >0.6 |

## Critères de Succès

- ✅ **PASS** : Sharpe réel ≥ attendu - 0.2
- ⚠️ **ADJUST** : Sharpe réel ≥ attendu - 0.5
- ❌ **FAIL** : Sharpe réel < attendu - 0.5 ou négatif

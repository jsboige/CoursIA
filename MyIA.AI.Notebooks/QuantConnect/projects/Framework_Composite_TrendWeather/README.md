# Framework_Composite_TrendWeather

**Classe d'actifs :** Actions US (ETF + actions)
**Cloud project ID :** Aucun (local uniquement)

## Description

Composite framework combinant TrendStocks (75 %) avec AllWeather (25 %). La composante
tendance utilise SMA200+EMA, AllWeather apporte la diversification.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_TrendWeather"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 1.155 |
| CAGR | 27.4 % |
| Max Drawdown | 27.7 % |
| Allocation | 75 % Trend / 25 % AllWeather |

## Fichiers

- `main.py` — Stratégie (composite T75/AW25 v1.5)

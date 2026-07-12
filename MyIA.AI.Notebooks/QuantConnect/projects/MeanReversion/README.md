# MeanReversion

**Classe d'actifs :** ETF sectoriels américains
**ID projet Cloud :** Aucun (local uniquement)

## Description

Stratégie de mean-reversion court terme sur 11 ETF sectoriels GICS (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC).
Achète les ETF les plus survendus (RSI(14) < 40) et conserve 15 jours ou jusqu'à RSI > 60.

Filtre de régime SMA200 sur SPY : sort de toutes les positions en marché baissier.
Stop-loss à -8 % pour couper les vraies ruptures. Maximum 4 positions simultanées à 25 % chacune.

## Comment lancer

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/MeanReversion"`
```bash
lean backtest --project .
```

**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour lancer.

## Métriques de backtest (2015-2026)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.294 |
| CAGR | 7.53 % |
| Max Drawdown | 16.5 % |
| Rendement net | +80.9 % |
| Rebalance | Scan quotidien |

## Fichiers

- `main.py` - Stratégie (v4.0, mean-reversion sur ETF sectoriels)
- `research.ipynb` - Optimisation RSI, stop-loss et tests de période de détention

## Références

- Jegadeesh (1990), « Evidence of Predictable Behavior of Security Returns »
- De Bondt & Thaler (1985), « Does the Stock Market Overreact? »

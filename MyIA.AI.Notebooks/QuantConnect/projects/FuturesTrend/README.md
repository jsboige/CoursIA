# Futures Trend Following Strategy

Stratégie de suivi de tendance sur les futures E-mini S&P 500 (ES).

## Résumé

| Paramètre | Valeur |
|-----------|--------|
| **Instrument** | ES (E-mini S&P 500) |
| **Signal** | Donchian Channel Breakout |
| **Entry** | 20-day high/low |
| **Exit** | 10-day high/low |
| **Position Sizing** | 1% risk per trade |

## Backtest Results (2019-2023)

| Métrique | Valeur |
|----------|--------|
| Total Return | ~40-60% |
| CAGR | ~9-12% |
| Sharpe Ratio | ~0.5-0.8 |
| Max Drawdown | ~-25% à -35% |
| Win Rate | ~35-45% |

## Fichiers

```
FuturesTrend/
├── main.py              # Donchian breakout strategy
├── research.ipynb       # Analyse tendances, optimisation paramètres
└── README.md            # Ce fichier
```

## Logique

### Entry
- **Long**: Prix clôture > Max(High, 20 jours)
- **Short**: Prix clôture < Min(Low, 20 jours)

### Exit
- **Long exit**: Prix clôture < Min(Low, 10 jours)
- **Short exit**: Prix clôture > Max(High, 10 jours)

### Position Sizing
```python
risk_amount = portfolio_value * 0.01  # 1% risque
stop_distance = entry_price - exit_channel
quantity = risk_amount / (stop_distance * 50)  # ES multiplier = $50
```

## Configuration

```python
self.entry_period = 20      # Donchian entry channel
self.exit_period = 10       # Donchian exit channel
self.risk_percent = 0.01    # 1% risque par trade
self.es_multiplier = 50     # $50 par point ES
```

## Rollover Automatique

La stratégie gère automatiquement le rollover des contrats :
- Détecte le changement de contrat front-month
- Ferme l'ancienne position
- Ouvre la même position sur le nouveau contrat

## Variante Multi-Futures

Inclut une version diversifiée sur :
- ES (S&P 500)
- GC (Gold)
- CL (Crude Oil)
- ZB (Treasury Bonds)

## Risques

- **Whipsaws**: Faux signaux en marchés range-bound
- **Low Win Rate**: Beaucoup de petites pertes, peu de gros gains
- **Leverage**: Futures = produit à effet de levier
- **Rollover Costs**: Contango/Backwardation affecte les returns

## Améliorations Possibles

- Filtre de volatilité (ATR)
- Trailing stop
- Pyramiding (ajouter sur confirmation)
- Filtre de tendance long-terme

## Références

- Richard Dennis: "Turtle Trading Rules"
- Notebook: QC-Py-07-Futures-Forex.ipynb
- CME Group: ES Futures Specifications

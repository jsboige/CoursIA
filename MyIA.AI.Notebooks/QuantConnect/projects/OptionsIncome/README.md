# Options Income Strategies

Stratégies de génération de revenus via la vente d'options.

## Stratégies Incluses

### 1. Covered Call (main.py)

| Paramètre | Valeur |
|-----------|--------|
| **Sous-jacent** | SPY (100 actions) |
| **Option** | Call OTM (delta ~0.30) |
| **Expiration** | ~30 jours |
| **Roll** | 7 jours avant expiration |

### 2. Iron Condor (inclus dans main.py)

| Paramètre | Valeur |
|-----------|--------|
| **Sous-jacent** | SPY |
| **Structure** | Short put spread + Short call spread |
| **Wings** | $5 de largeur |
| **Expiration** | ~30 jours |

## Backtest Results - Covered Call (2020-2023)

| Métrique | Valeur |
|----------|--------|
| Total Return | ~25-35% |
| Premium Collected | ~$8,000-12,000 |
| Max Drawdown | ~-25% à -30% |
| Sharpe Ratio | ~0.5-0.8 |

## Fichiers

```
OptionsIncome/
├── main.py              # Covered Call + Iron Condor
├── research.ipynb       # Analyse options, Greeks, backtest
└── README.md            # Ce fichier
```

## Configuration Options

```python
# Covered Call
self.target_delta = 0.30        # Delta cible (probabilité ITM ~30%)
self.days_to_roll = 7           # Jours avant expiration pour roll

# Iron Condor
self.put_delta = -0.15          # Delta short put
self.call_delta = 0.15          # Delta short call
self.wing_width = 5             # Largeur des wings ($5)
```

## Points Clés

### Covered Call
- **Profit max**: Strike - Prix d'achat + Premium
- **Perte max**: Prix d'achat - Premium (comme détenir l'action)
- **Idéal**: Marchés légèrement haussiers à neutres

### Iron Condor
- **Profit max**: Premium net collecté
- **Perte max**: Largeur wing - Premium
- **Idéal**: Marchés range-bound, faible volatilité

## Risques

- **Covered Call**: Perte illimitée à la baisse, upside limité
- **Iron Condor**: Perte si mouvement directionnel fort
- **Assignment**: Options américaines peuvent être exercées tôt
- **Liquidité**: Vérifier open interest > 100

## Améliorations Possibles

- Delta dynamique basé sur VIX
- Roll "up and out" si très bullish
- Gestion de la gamma risk proche expiration
- Stop-loss basé sur % du premium

## Références

- Notebook: QC-Py-06-Options-Trading.ipynb
- CBOE: Options Strategy Guide

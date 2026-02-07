# Momentum Universe Selection Strategy

Stratégie de sélection d'univers basée sur le momentum 12 mois.

## Résumé

| Paramètre | Valeur |
|-----------|--------|
| **Type** | Equity Long-Only |
| **Universe** | US Large Caps (>$1B market cap) |
| **Signal** | Momentum 12 mois |
| **Positions** | Top 20 |
| **Rebalancement** | Mensuel |
| **Allocation** | Equal-weight (5% par position) |

## Backtest Results (2018-2023)

| Métrique | Valeur |
|----------|--------|
| Total Return | ~65-85% |
| CAGR | ~11-14% |
| Sharpe Ratio | ~0.8-1.0 |
| Max Drawdown | ~-30% à -35% |
| Win Rate | ~55-60% |

## Fichiers

```
MomentumStrategy/
├── main.py              # Algorithme principal
├── research.ipynb       # Notebook de recherche (analyse momentum)
└── README.md            # Ce fichier
```

## Paramètres Configurables

```python
self.num_coarse = 500        # Filtrage initial par liquidité
self.num_fine = 20           # Nombre de positions finales
self.momentum_period = 252   # Période momentum (252 = 12 mois)
```

## Logique

1. **Coarse Filter**: Top 500 par dollar volume quotidien
2. **Fine Filter**: Calcul momentum = (Prix actuel - Prix 12 mois) / Prix 12 mois
3. **Selection**: Top 20 par momentum
4. **Rebalancement**: Premier jour de chaque mois
5. **Allocation**: 5% par position (equal-weight)

## Risques

- **Momentum Crash**: Peut sous-performer fortement lors de retournements de marché
- **High Turnover**: ~40-60% de rotation mensuelle = frais de transaction
- **Concentration**: 20 positions = risque spécifique significatif

## Améliorations Possibles

- Ajouter filtre macro (SPY > SMA 200)
- Combiner momentum court-terme et long-terme
- Pondération par volatilité inverse (risk parity)
- Stop-loss dynamique

## Références

- Jegadeesh & Titman (1993): "Returns to Buying Winners and Selling Losers"
- Notebook: QC-Py-05-Universe-Selection.ipynb

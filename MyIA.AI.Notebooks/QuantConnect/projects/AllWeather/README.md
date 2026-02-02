# All-Weather Portfolio Strategy

Portfolio multi-asset inspiré de Ray Dalio (Bridgewater Associates).

## Résumé

| Paramètre | Valeur |
|-----------|--------|
| **Type** | Multi-Asset |
| **Rebalancement** | Trimestriel |
| **Classes d'actifs** | Actions, Bonds, Or, Commodities |
| **Objectif** | Stabilité dans tous les environnements |

## Allocation Standard

| Actif | Allocation | ETF | Rôle |
|-------|------------|-----|------|
| Actions US | 30% | SPY | Croissance |
| Bonds Long-terme | 40% | TLT | Déflation, récession |
| Bonds Intermédiaires | 15% | IEF | Stabilité |
| Or | 7.5% | GLD | Inflation, crise |
| Commodities | 7.5% | DBC | Inflation |

## Backtest Results (2015-2023)

| Métrique | Valeur |
|----------|--------|
| Total Return | ~80-100% |
| CAGR | ~8-10% |
| Sharpe Ratio | ~0.7-1.0 |
| Max Drawdown | ~-15% à -20% |
| Volatilité | ~8-10% |

## Fichiers

```
AllWeather/
├── main.py              # Portfolio standard + Risk Parity + Tactical
├── research.ipynb       # Analyse corrélations, backtest allocations
└── README.md            # Ce fichier
```

## Variantes Incluses

### 1. Standard All-Weather
- Allocation fixe (30/40/15/7.5/7.5)
- Rebalancement trimestriel
- Seuil de drift 5%

### 2. Risk Parity
- Pondération par volatilité inverse
- Contribution égale au risque
- Favorise les bonds (faible vol)

### 3. Tactical Overlay
- Réduit l'allocation si prix < SMA 200
- Augmente le cash en période de stress
- Trade-off: moins de drawdown, moins de return

## Configuration

```python
# Allocations cibles
self.target_allocations = {
    "SPY": 0.30,   # 30% Actions
    "TLT": 0.40,   # 40% Bonds long-terme
    "IEF": 0.15,   # 15% Bonds intermédiaires
    "GLD": 0.075,  # 7.5% Or
    "DBC": 0.075   # 7.5% Commodities
}

# Paramètres
self.rebalance_threshold = 0.05  # Rebalancer si drift > 5%
```

## Philosophie

L'All-Weather est conçu pour performer dans 4 environnements :

| Environnement | Actifs performants |
|---------------|-------------------|
| Croissance ↑ | Actions |
| Croissance ↓ | Bonds |
| Inflation ↑ | Or, Commodities |
| Inflation ↓ | Bonds |

## Risques

- **Sous-performance en bull market**: Trop de bonds dilue les gains
- **Sensibilité aux taux**: Bonds souffrent quand les taux montent
- **Corrélations instables**: En crise, tout peut baisser ensemble
- **Commodities roll yield**: Contango érode les returns long-terme

## Améliorations Possibles

- Ajouter TIPS (Treasury Inflation-Protected Securities)
- Diversification géographique (VEA, VWO)
- Dynamic risk targeting
- Factor tilts (Value, Momentum)

## Références

- Ray Dalio: "Principles" (chapitre sur l'All-Weather)
- Bridgewater Associates: "The All Weather Story"
- Notebook: QC-Py-08-Multi-Asset-Strategies.ipynb

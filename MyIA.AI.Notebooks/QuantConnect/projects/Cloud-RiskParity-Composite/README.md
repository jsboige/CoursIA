# Cloud-RiskParity-Composite

**Classe d'actifs :** Multi-actifs (Actions, Obligations, Matières premières)

**ID projet Cloud :** N/A

## Description

Rotation tactique à travers six classes d'actifs (SPY, TLT, GLD, EFA, EEM, DBC) en utilisant un double filtre : prix au-dessus du SMA200 ET momentum positif sur 6 mois. Les actifs passant les deux filtres reçoivent une pondération égale. Rebalance tous les 30 jours. Inspiré de l'approche de trend-following avec allocation en parité de risque de Hurst, Ooi et Pedersen (2014) chez AQR.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Cloud-RiskParity-Composite/main.py
```

### QC Cloud
Créer un nouveau projet, téléverser `main.py`, compiler et lancer un backtest (défaut : 2015-01-01 au 2024-12-31).

## Métriques de backtest

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| Parité de risque à double filtre | 30 jours | SMA200 + momentum 6 mois, pondération égale entre les actifs retenus |

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Rotation parité de risque avec double filtre SMA200 + momentum sur 6 ETF multi-actifs |

## Références

- Hurst, B., Ooi, Y.H., Pedersen, L.h. (2014). *A Century of Evidence on Trend-Following Investing*. AQR.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)

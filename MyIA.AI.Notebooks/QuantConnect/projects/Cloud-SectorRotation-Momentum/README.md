# Cloud-SectorRotation-Momentum

**Classe d'actifs :** Actions, Obligations, Matières premières (rotation d'ETF)

**ID projet Cloud :** N/A

## Description

Trend-following pondéré par momentum sur un univers de 5 ETF (QQQ, SPY, EFA, GLD, IWM) avec SHY comme équivalent cash défensif. Utilise un double filtre (prix au-dessus du SMA200 ET momentum positif sur 6 mois) pour sélectionner les actifs en tendance, puis alloue proportionnellement à leurs scores de momentum mesurés par taux de variation (ROC). Rebalance tous les 21 jours de bourse.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Cloud-SectorRotation-Momentum/main.py
```

### QC Cloud
Créer un nouveau projet, téléverser `main.py`, compiler et lancer un backtest (défaut : 2015-01-01 au 2024-12-31).

## Métriques de backtest

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| Trend-following pondéré par momentum | 21 jours | Double filtre SMA200 + momentum 6 mois, pondération proportionnelle au ROC |

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Rotation sectorielle avec allocation pondérée par momentum et double filtre de tendance |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)

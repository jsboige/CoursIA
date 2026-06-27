# Cloud-MeanReversion-Sectors

**Classe d'actifs :** Actions (ETF sectoriels GICS)

**ID projet Cloud :** N/A

## Description

Stratégie de retour à la moyenne basée sur le RSI(14) sur 11 ETF sectoriels GICS (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC). Trois variantes de sophistication croissante : v1 utilise des signaux bruts de survente/surachat du RSI ; v2 ajoute un filtre de régime SMA200 (ne trader qu'en marché haussier) ; v3 incorpore des règles de stop-loss. Scan quotidien 30 minutes après l'ouverture du marché.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Cloud-MeanReversion-Sectors/main.py
```

### QC Cloud
Créer un nouveau projet, téléverser `main.py`, compiler et lancer un backtest (défaut : 2015-01-01 au 2024-12-31).

## Métriques de backtest

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| Retour à la moyenne RSI (3 variantes) | Scan quotidien | RSI période 14, filtre de régime SMA200 (v2+), stop-loss (v3) |

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Algorithme de retour à la moyenne avec 3 variantes (RSI, +filtre de régime, +stop-loss) sur 11 ETF sectoriels |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)

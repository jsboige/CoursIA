# Cloud-VolTargeting

**Classe d'actifs :** Multi-actifs (Actions, Obligations, Matières premières)

**ID projet Cloud :** N/A

## Description

Stratégie de ciblage de volatilité avec trois variantes. v1 cible 12 % de volatilité annualisée sur SPY seul via une mise à l'échelle par volatilité réalisée. v2 étend à un portefeuille multi-actifs (SPY, QQQ, IEF, GLD) avec une contribution en risque égale ciblant 10 % de volatilité annualisée. v3 ajoute un filtre de momentum sur 126 jours à l'approche multi-actifs. Rebalance mensuelle pour toutes les variantes.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Cloud-VolTargeting/main.py
```

### QC Cloud
Créer un nouveau projet, téléverser `main.py`, compiler et lancer un backtest (défaut : 2015-01-01 au 2024-12-31).

## Métriques de backtest

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| Ciblage de volatilité (3 variantes) | Mensuelle | Cible de vol 10-12 %, filtre momentum 126 jours (v3), contribution en risque égale (v2/v3) |

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Algorithme de ciblage de volatilité avec 3 variantes (actif unique, multi-actifs ERC, +momentum) |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)

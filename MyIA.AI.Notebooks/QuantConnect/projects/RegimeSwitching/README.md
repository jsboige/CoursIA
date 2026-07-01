# RegimeSwitching

**Classe d'actifs :** Actions/ETF américains
**ID projet Cloud :** Aucun (local uniquement)

## Description

Basculage de régime momentum/mean-reversion par croisement SMA50/SMA200. Applique le momentum en tendance, la mean-reversion en range.

## Comment lancer

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/RegimeSwitching"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour lancer.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Méthode | Bascule de régime SMA50/200 |
| Stratégies | Momentum + Mean-reversion |

## Fichiers

- `main.py` - Stratégie (iter3, bascule de régime)

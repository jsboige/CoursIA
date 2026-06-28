# SectorMomentum

**Classe d'actifs :** Actions US + Bonds + Or (SPY, TLT, GLD)
**ID projet Cloud :** Aucun (local uniquement)
**Statut :** ARCHIVÉE (plafond de Sharpe ~0,56)

## Description

Stratégie de dual momentum avec score composite multi-lookback (1, 3, 6, 12 mois, poids 0,4/0,2/0,2/0,2) sur 3 actifs : SPY (risk-on), TLT (bonds), GLD (or).

Quand SPY a un momentum absolu positif ET se situe au-dessus de sa SMA200 ET surperforme TLT/GLD : position 100 % SPY.
Sinon : rotation vers l'actif défensif le plus performant (TLT ou GLD).
Protection de sortie SMA200 quotidienne (stops intra-mensuels si SPY passe sous la SMA200).

**Archivée car :** plafond de Sharpe ~0,56 pour le dual momentum sur 3-5 actifs. La cible de 0,8 exige une approche fondamentalement différente. Voir ARCHIVE.md pour le détail complet.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/SectorMomentum"`
```bash
lean backtest --project .
```

**QC Cloud :** Pas encore déployée. Copier les fichiers dans un nouveau projet QC Cloud pour l'exécuter.

## Métriques de backtest (2015-2026)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0,555 |
| CAGR | 13,0 % |
| Max Drawdown | 22,8 % |
| Rebalance | Mensuel (entrées), Quotidien (sortie SMA200) |

## Fichiers

- `main.py` - Stratégie (v3.2, confirmée comme la meilleure)
- `research.ipynb` - Optimisation multi-lookback et tests d'univers étendu

## Références

- Antonacci (2014), « Dual Momentum Investing »
- Faber (2007), « A Quantitative Approach to Tactical Asset Allocation »
- ARCHIVE.md - Historique complet des itérations et analyse du plafond

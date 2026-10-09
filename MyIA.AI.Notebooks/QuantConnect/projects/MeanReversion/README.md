# MeanReversion

**Classe d'actifs :** ETF sectoriels américains
**ID projet Cloud :** Aucun (local uniquement)

## Description

Stratégie de mean-reversion court terme sur 11 ETF sectoriels GICS (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC).
Achète les ETF les plus survendus (RSI(14) < 40) et conserve 15 jours ou jusqu'à RSI > 60.

Filtre de régime SMA200 sur SPY : sort de toutes les positions en marché baissier.
Stop-loss à -8 % pour couper les vraies ruptures. Maximum 4 positions simultanées à 25 % chacune.

## Comment lancer

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/MeanReversion"`
```bash
lean backtest --project .
```

**QC Cloud :** Pas de projet cloud persistant ; un backtest de sweep est enregistré — verdict **BROKEN** (`docs/qc/qc-strategies-status.md` l.186). Copier les fichiers dans un nouveau projet QC Cloud pour relancer.

## Métriques (backtest QC Cloud — sweep #1621, tranche 4)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | −0.082 |
| CAGR | 3.00 % |
| Max Drawdown | 17.5 % |
| PSR | 1.3 % |
| Fenêtre | 2845 j. |

Verdict : **BROKEN** — Sharpe négatif, edge nul. Reproduction QuantBook sur le code v4.0 local (`quantbook.ipynb`, cellule d'en-tête) : Sharpe 0.365, CAGR 7.2 %, MaxDD 14.7 % — plus favorable que le run cloud de sweep.

## Fichiers

- `main.py` - Stratégie (v4.0, mean-reversion sur ETF sectoriels)
- `research.ipynb` - Recherche : pivot stocks -> ETF sectoriels, hypothèses H1-H8 (RSI, stop-loss, période de détention...)
- `quantbook.ipynb` - Reproduction QuantBook de l'analyse exploratoire sur les ETF sectoriels (données natives QC)

## Références

- Jegadeesh (1990), « Evidence of Predictable Behavior of Security Returns »
- De Bondt & Thaler (1985), « Does the Stock Market Overreact? »

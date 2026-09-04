# AssetClassMomentum-QC

**Asset class:** Multi-Asset (ETF universe)
**Cloud project ID:** 33209767 (`AssetClassMomentum-QC-baseline`)

## Description

Cross-asset ETF momentum rotation, v2.0 consolidée depuis l'article QC research
**#21050** « Cross-Asset ETF Momentum with a Correlation-Based Short Hedge »
(Derek Melchin, 2026-07) — issue #14091, EPIC #11698. Source primaire :
Pauchlyová & Vojtko (2025), *Refining ETF Asset Momentum Strategy*, Quantpedia /
SSRN [5095447](https://ssrn.com/abstract=5095447).

**v2.0 — moteur :**
1. **Univers 13 ETFs** : SPY, IWM, EFA, EEM, IYR, QQQ, LQD, IEF, TIP, GLD, USO,
   DBC, FXE.
2. **Momentum multi-horizon** : moyenne des ROC 3/6/9/12 mois (63/126/189/252 j).
3. **Top-4 en long équipondéré** (25 % chacun), rebalance le 1ᵉʳ jour ouvré du mois.
4. **Hedge court gated par corrélation** : quand la corrélation moyenne des 78
   paires sur 20 j dépasse celle sur 250 j (régime défavorable), short -30 % de
   l'ETF au momentum le plus faible → 130 % brut / 70 % net ; sinon 100 %
   long-only.

v1 (baseline, tranche 3 #1621) : clone QC Strategy Library (5 ETFs, momentum 12 m,
top-3, sans hedge) — Needs-improvement : Sharpe 0.22 / CAGR 6.64 % / MaxDD 28.1 % /
PSR 3.8 % (2018-2025).

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/AssetClassMomentum-QC"`
**QC Cloud:** projet 33209767 — dates paramétrables `start_date` / `end_date`
(défaut 2016-01-01 → 2026-07-01).

## Backtest Metrics

| Metric | Dev 2016-2021 | OOS 2022-2026 | Full 2016-2026 |
|--------|---------------|---------------|----------------|
| Sharpe Ratio | **0.712** | **0.035** | **0.423** |
| CAGR | 13.596 % | 6.212 % | 10.535 % |
| Max Drawdown | 21.800 % | 19.800 % | 21.800 % |
| Net Profit | 114.996 % ($82 103) | 31.159 % ($29 062) | 186.431 % ($181 895) |
| PSR | 16.961 % | 0.646 % | 0.981 % |

**Verdict honnête** : amélioration nette vs v1 sur la gestion du risque (MaxDD
28.1 % → 21.8 %) et le Sharpe pleine période (0.22 sur 2018-2025 → 0.42 sur
2016-2026), cohérente avec l'article (Sharpe 0.498 vs SPY 0.407 sur 2007-2026).
**Mais l'OOS 2022-2026 ne confirme pas d'edge statistique** (Sharpe 0.035,
PSR 0.65 %) — le régime de taux 2022+ défavorable au momentum cross-asset
frappe aussi la version hedgée. Statut #1621 : Needs-improvement (amélioré,
pas d'edge OOS confirmé).

Référence article (#21050, 2007-07 → 2026-06) : Sharpe 0.498 (avec hedge) vs
0.451 (long-only) vs 0.407 (SPY buy-and-hold).

## Files

- main.py - Strategy v2.0 (consolidation article #21050)

## References

- QuantConnect research #21050 — Cross-Asset ETF Momentum with a Correlation-Based Short Hedge
- Pauchlyová & Vojtko (2025), Quantpedia / SSRN 5095447
- Issue #14091 (verdict CONSOLIDATION), EPIC #11698

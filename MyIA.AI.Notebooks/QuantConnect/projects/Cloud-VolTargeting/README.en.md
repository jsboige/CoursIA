# Cloud-VolTargeting

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** 30823587

## Description

Volatility targeting strategy with three variants. v1 targets 12% annualized volatility on SPY alone using realized vol scaling (log-returns × √252 over 21 days). v2 extends to a multi-asset portfolio (SPY, QQQ, IEF, GLD) with equal risk contribution targeting 10% annualized vol. v3 adds a 126-day momentum filter to the multi-asset approach, with a defensive retreat to IEF. Monthly rebalance across all variants. Interactive Brokers brokerage (real costs), SPY benchmark.

## How to Run

### Lean CLI

```bash
lean backtest --algorithm Cloud-VolTargeting/main.py
```

### QC Cloud

Project 30823587. Upload `main.py`, compile and run a backtest. Hard-coded period: **2018-01-01 → 2025-01-01** (aligned with the cross-strategy baseline #1630). The default variant (`version=1`, SPY only) is backtested below; pass `version=2` or `3` for the multi-asset variants.

## Backtest Metrics

Run le plus récent via QC Cloud MCP, 2026-10-20 (`main.py` tel que committé, projet 30823587, compile `BuildSuccess`, backtest `21585-v1-warmup-2018-2025` = `cc01cc58067e2021aadfa3c1dbb3fb1c`, 1761 dates négociables, 84 ordres) :

| Indicator | Value | Reading |
|---|---|---|
| Sharpe ratio | **0.438** | weakly positive |
| CAGR | **10.845%** | sous le buy-hold SPY, dividendes réinvestis (13,731 % sur la même fenêtre) |
| Max drawdown | **21.000%** | sous SPY (33,717 % au krach COVID 2020) |
| Total net profit | **105.691%** (+$105,691.36) | equity finale 205 691,36 $ ; la part réalisée seule est de 77 750,40 $ |
| PSR (Probabilistic Sharpe Ratio) | **3.263%** | indistinguable du bruit |
| Orders | 84 | very low turnover (monthly) |

**Verdict : NO-BEATS.** Le vol targeting sur SPY seul ne bat pas le buy-and-hold SPY : CAGR 10,8 % contre 13,7 %, Sharpe sous celui du benchmark, PSR 3,3 % — indistinguable du bruit. Ce qu'il achète en échange n'est pas le rendement ajusté du risque mais le drawdown (21,0 % contre 33,7 %).

Sous-performance et significativité sont mesurées séparément, pas confondues :

- **Rendements excédentaires** — test apparié des 1756 séances où les deux jambes sont observées (bootstrap circulaire par blocs de 21 séances, 10 000 tirages, graine 18921, instrument `voltarget_strategy_verdict.circular_block_diff` du dépôt) : différence de Sharpe **-0,015**, **p unilatérale 0,556**, IC 95 % [-0,374 ; +0,307]. La sous-performance cumulée est réelle (+106,5 % contre +146,9 % pour SPY sur la fenêtre) ; la différence de Sharpe, elle, est du bruit.
- **PSR de QC** — 3,263 % : le Sharpe 0,438 n'est pas distinguable du bruit.

Fenêtre longue 2007-2026 (`21585-v1-warmup-oos` = `f3839e9e82a78d83bb45d37045864c6e`, 4946 dates négociables, 235 ordres) : Sharpe 0,488, CAGR 10,630 %, drawdown max 31,300 %, profit net 630,024 % (+630 024,26 $), PSR 0,229 % — même verdict. Aucune jambe SPY n'y est disponible (le run frère qui expose `set_benchmark("SPY")` porte la fenêtre alignée 2018-2025), donc le test apparié n'y est pas calculé et la PSR de QC y reste le seul instrument de significativité.

### Effet des correctifs sur ces chiffres (#18941 puis #21585)

Les deux runs ci-dessous ne diffèrent que par `set_warm_up(21, Resolution.DAILY)` et la garde `is_warming_up` dans `rebalance()` :

| Fenêtre | Run | Ordres | Sharpe | CAGR | Drawdown max | Profit net | PSR |
|---|---|---|---|---|---|---|---|
| 2018-2025, avant | `18941-v1-after-2018-2025` (`695126a305a6fc3e52191c81733958f3`) | 83 | 0,382 | 9,761 % | 20,900 % | 92,011 % (+92 010,66 $) | 2,227 % |
| 2018-2025, après | `21585-v1-warmup-2018-2025` (`cc01cc58067e2021aadfa3c1dbb3fb1c`) | **84** | 0,438 | 10,845 % | 21,000 % | 105,691 % (+105 691,36 $) | 3,263 % |
| 2007-2026, avant | `18941-v1-after-oos` (`eea534fd4d223287fd446db6b56befb8`) | 234 | 0,478 | 10,448 % | 31,200 % | 606,809 % (+606 809,12 $) | 0,197 % |
| 2007-2026, après | `21585-v1-warmup-oos` (`f3839e9e82a78d83bb45d37045864c6e`) | **235** | 0,488 | 10,630 % | 31,300 % | 630,024 % (+630 024,26 $) | 0,229 % |

Le montant en dollars est la variation d'equity (part réalisée + latente), homologue du pourcentage de profit net **total**. QC publie par ailleurs « Net Profit », qui ne compte que la part **réalisée** (65 999,11 $ et 77 750,40 $ pour les deux runs 2018-2025, l'écart valant exactement l'« Unrealized » publié) : les deux ne se mélangent pas dans une même ligne.

Le correctif récupère **un rééquilibrage par fenêtre** (83 → 84 et 234 → 235 ordres) : la première séance du run déclenchait le rééquilibrage mensuel (`date_rules.month_start("SPY")`, correctif #18941) avant que SPY n'ait reçu sa première barre ; l'ordre partait à un prix nul et QuantConnect le rejetait, la courbe restait plate jusqu'au mois suivant. Sans warm-up, janvier 2018 se passait donc en liquidités — mois où SPY a rendu 5,5 % — et l'equity finale porte cet écart composé sur sept ans (192 010,66 $ contre 205 691,36 $).

Le tableau publié ici jusqu'au 2026-10-20 (Sharpe 0,207, CAGR 6,717 %, drawdown 38,200 %, profit net 57,671 %, PSR 0,557 %, 54 ordres, run `VolTargeting-v1-honest-read-2026-08` du 2026-08-07) datait d'**avant ces deux correctifs** : #18941 d'abord (le rééquilibrage mensuel sautait les mois dont le 1er n'est pas un jour de bourse : 54 → 83 ordres), #21585 ensuite. L'écart est attribué aux correctifs, non à un re-tuning : les paramètres de la stratégie sont inchangés et le verdict honnête reste le même.

Les runs `18941-v1-after-*` (avant warm-up) portaient en outre le test de significativité des rendements excédentaires de QuantConnect : p = 0,0594 sur 2018-2025 et p = 0,298 sur 2007-2026, tous deux > 0,05 — le verdict NO-BEATS tenait déjà avant ce correctif.

## Honest read (v1 variant)

v1 scales the SPY allocation from realized volatility: `allocation = vol_target / realized_vol`, clamped between 30% and 150%. Weaknesses observed over 2018-2025:

- **Lagged signal (volatility lag).** Realized volatility typically rises **after** a drawdown begins (2020 COVID crash, 2022 bear). The allocation cut therefore arrives too late to avoid the loss tail, but in time to miss the ensuing rebound.
- **30% exposure floor.** Even in high volatility, the strategy stays at least 30% invested — downside protection is partial, while upside return is curtailed.
- **Leverage in calm periods.** `max_allocation = 1.50` adds leverage when vol is low (bull markets), increasing risk without a proportional Sharpe improvement.
- **PSR ≈ 3%.** The 0.438 Sharpe is not statistically significant: indistinguishable from noise. Any edge claim would be misleading (rule C, PR-review-discipline §C).

The v2 (multi-asset diversification + equal risk contribution) and v3 (+ momentum + IEF defensive) variants aim to correct these weaknesses (diversifying reduces drawdown, momentum filters declining assets), but are not backtested here: an honest read documents the baseline variant and its honest verdict, without re-tuning. Re-optimizing the vol target, lookback, or allocation bounds to recover a positive Sharpe on this single window would be overfitting until proven otherwise (EPIC #9768, D2 "unfixed window"). The strategy is shipped with its parameters coded as-is, honest verdict rendered.

## Files

| File | Description |
|------|-------------|
| `main.py` | Volatility targeting with 3 variants (v1 SPY only, v2 multi-asset equal-risk, v3 +momentum +IEF defensive) |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
- QC / Trading consolidation EPIC: #1621
- Governed by EPIC #9768 (backtest-metric drift across revisions)

See #1621 (partial contribution: honest-read of a previously-unaudited strategy).

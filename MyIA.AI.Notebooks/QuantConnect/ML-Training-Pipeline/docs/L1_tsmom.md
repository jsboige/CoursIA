# L1 — TSMOM Baseline Multi-Assets (Panier Anti-Biais 25 Symboles)

## Verdict: NO BEATS

Time-Series Momentum (Moskowitz-Ooi-Pedersen 2012) on 25-symbol anti-bias panier
(7 asset classes, NO FAANG/Mag7). **All lookbacks fail to beat equal-weight buy-and-hold.**

## Method

- **Signal**: sign(past return) at lookbacks 21/63/126/252 days
- **Position sizing**: volatility-scaled to 15% annualized target
- **Portfolio**: equal-weight across assets
- **Validation**: walk-forward expanding, 5 folds, gap=21d
- **Seeds** (live, #14470): each seed draws a 21-symbol sub-basket (80% of 26,
  without replacement) + an origin offset of 0-40 business days; the SAME view
  feeds TSMOM and its B&H baseline (paired comparison)
- **Transaction costs** (#14470): proportional to the notional actually moved
  (daily turnover, `sum |Δposition|`), at 5bps equity / 10bps crypto / 50bps
  stress. The legacy L1 convention (one full round-trip per moving line per
  day) is kept as the diagnostic column `Net Sharpe (L1 conv.)`
- **Benchmark**: equal-weight buy-and-hold (Sharpe 1.09, per-seed views)

## Results

| Lookback | Gross Sharpe | Net Sharpe | Net Sharpe (L1 conv.) | B&H Sharpe | Delta | Avg daily turnover | Verdict |
|----------|-------------|-----------|----------------------|-----------|-------|--------------------|---------|
| 21d      | 0.51        | 0.43      | -2.42                | 1.09      | -0.66 | 0.18               | NO BEATS |
| 63d      | 0.52        | 0.49      | -2.41                | 1.09      | -0.60 | 0.09               | NO BEATS |
| 126d     | 0.84        | 0.81      | -2.20                | 1.09      | -0.28 | 0.07               | NO BEATS |
| 252d     | 0.75        | 0.73      | -2.28                | 1.09      | -0.36 | 0.05               | NO BEATS |
| 126d stress | 0.84     | 0.62      | -19.07               | 1.09      | -0.47 | 0.07               | NO BEATS |
| 126d stress | 0.81     | -19.13    | 1.15      | -20.28| 5519   | NO BEATS |

## Key Findings

1. **The verdict does not change, but the margin does**. Under the turnover-proportional
   cost convention (#14470), TSMOM is net-positive (0.43-0.81) instead of deeply negative,
   yet still fails to beat B&H by -0.28 to -0.66 Sharpe. The `Net Sharpe (L1 conv.)`
   column shows what the legacy full round-trip-per-moving-line convention billed — that
   convention overstated rebalancing cost and was the sole source of the previously
   published deeply-negative net Sharpes.

2. **Costs still drag, but proportionally to what is moved**. Daily rebalancing moves
   0.05-0.18 of notional per day (vol-scaled weights drift); at 5-10bps this costs
   0.02-0.11 Sharpe, not the 3+ Sharpe the legacy convention implied. Testing the
   article's monthly rebalancing remains the open question (out of scope here, cf #14470
   third lead).

3. **Longer lookbacks do better** (126d net 0.81 vs 21d net 0.43) — fewer position flips
   and a more stable signal.

4. **B&H benchmark is strong** (Sharpe 1.09) because the panier includes the 2015-2025
   bull market in equities + crypto. Active strategies face a high hurdle.

5. **The multi-seed gate now measures something** (#14470). Before the fix, the seed
   loop built an rng that was never consumed: the 4 seeds ran byte-identical
   computations, cross-seed std was exactly 0, and the `t_stat >= 2.0` BEATS gate was
   structurally unreachable. Live sub-basket + origin-offset views give per-seed
   dispersion (t-stats -7.1 to -14.8 on this run) — the gate can now, in principle,
   return BEATS.

## Data

- 25 of 26 panier symbols loaded (VIX excluded as it has no price return)
- Date range: 2015-01-02 to 2026-05-23
- OOS observations: ~1650 per seed (varies slightly with the seed's origin offset)

## Script

`scripts/L1_tsmom.py` — outputs to `checkpoints/l1_tsmom/L1_tsmom_results.json`

## Implication for Ladder

TSMOM = baseline floor. Any ML model (L2 cross-sectional, L3 directional) must beat
both this TSMOM AND the B&H benchmark to be considered useful. The high B&H Sharpe
(1.15) sets a demanding bar for L2/L3.

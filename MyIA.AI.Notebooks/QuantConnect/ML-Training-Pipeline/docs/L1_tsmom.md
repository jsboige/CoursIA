# L1 — TSMOM Baseline Multi-Assets (Panier Anti-Biais 25 Symboles)

## Verdict: NO BEATS

Time-Series Momentum (Moskowitz-Ooi-Pedersen 2012) on 25-symbol anti-bias panier
(7 asset classes, NO FAANG/Mag7). **All lookbacks fail to beat equal-weight buy-and-hold.**

## Method

- **Signal**: sign(past return) at lookbacks 21/63/126/252 days
- **Position sizing**: volatility-scaled to 15% annualized target
- **Portfolio**: equal-weight across assets
- **Validation**: walk-forward expanding, 5 folds, gap=21d
- **Transaction costs**: 5bps equity, 10bps crypto, 50bps stress test
- **Benchmark**: equal-weight buy-and-hold (Sharpe 1.15)

## Results

| Lookback | Gross Sharpe | Net Sharpe | B&H Sharpe | Delta | Trades | Verdict |
|----------|-------------|-----------|-----------|-------|--------|---------|
| 21d      | 0.18        | -2.56     | 1.15      | -3.71 | 5519   | NO BEATS |
| 63d      | 0.15        | -2.40     | 1.15      | -3.55 | 5519   | NO BEATS |
| 126d     | 0.12        | -2.26     | 1.15      | -3.41 | 5519   | NO BEATS |
| 252d     | 0.14        | -2.37     | 1.15      | -3.52 | 5519   | NO BEATS |
| 126d stress | 0.81     | -19.13    | 1.15      | -20.28| 5519   | NO BEATS |

## Key Findings

1. **TSMOM is profitable gross but destroyed by costs**. Even moderate costs (~5-10bps)
   erase the thin momentum signal, producing deeply negative net Sharpe.

2. **High trade frequency kills performance**. TSMOM generates ~5500 trades over the
   OOS period (daily rebalancing across 25 assets). Daily position changes compound costs.

3. **Longer lookbacks slightly reduce losses** (126d: -2.26 vs 21d: -2.56) because
   fewer position flips, but still deeply negative.

4. **B&H benchmark is strong** (Sharpe 1.15) because the panier includes the 2015-2025
   bull market in equities + crypto. Active strategies face a high hurdle.

## Data

- 25 of 26 panier symbols loaded (VIX excluded as it has no price return)
- Date range: 2015-01-02 to 2026-05-23
- OOS observations: 1656 per seed

## Script

`scripts/L1_tsmom.py` — outputs to `checkpoints/l1_tsmom/L1_tsmom_results.json`

## Implication for Ladder

TSMOM = baseline floor. Any ML model (L2 cross-sectional, L3 directional) must beat
both this TSMOM AND the B&H benchmark to be considered useful. The high B&H Sharpe
(1.15) sets a demanding bar for L2/L3.

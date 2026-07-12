# L2 — Cross-Sectional + Dual Momentum (Panier Anti-Biais 25 Symboles)

## Verdict: NO BEATS

Both cross-sectional and dual momentum strategies fail to beat equal-weight buy-and-hold
on the 25-symbol anti-bias panier. However, they massively outperform L1 TSMOM.

## Method

- **Cross-sectional momentum**: rank assets by past return, long top-5, monthly rebalancing
- **Dual momentum (Antonacci)**: same as cross-sectional + absolute momentum filter (cash if negative)
- Cash proxy: SHY (short-term Treasury)
- Vol-unscaled (equal weight within selected assets)
- Walk-forward expanding 5-fold, gap=21d, 4 seeds (0/1/7/42)
- Transaction costs: 5bps equity, 10bps crypto

## Results

| Strategy | Lookback | Gross Sharpe | Net Sharpe | B&H Sharpe | Delta | Trades | Verdict |
|----------|----------|-------------|-----------|-----------|-------|--------|---------|
| Cross-sectional | 63d | 0.681 | 0.662 | 1.150 | -0.488 | 205 | NO BEATS |
| Cross-sectional | 126d | 0.952 | 0.935 | 1.150 | -0.216 | 161 | NO BEATS |
| Cross-sectional | 252d | 1.019 | 0.997 | 1.150 | -0.153 | 143 | NO BEATS |
| Dual momentum | 63d | 0.713 | 0.679 | 1.150 | -0.471 | 174 | NO BEATS |
| Dual momentum | 126d | 0.648 | 0.618 | 1.150 | -0.533 | 138 | NO BEATS |
| Dual momentum | 252d | 0.668 | 0.628 | 1.150 | -0.522 | 120 | NO BEATS |

## Comparison vs L1 TSMOM

| Metric | L1 TSMOM (best) | L2 CS (best) | L2 DM (best) |
|--------|----------------|-------------|-------------|
| Net Sharpe | -2.26 (126d) | 0.997 (252d) | 0.679 (63d) |
| Delta vs B&H | -3.41 | -0.153 | -0.471 |
| Trades | 5519 | 143 | 174 |

L2 cross-sectional improves by +3.26 Sharpe over L1 TSMOM. Monthly rebalancing
(143 trades vs 5519) dramatically reduces cost drag.

## Key Findings

1. **Cross-sectional > dual momentum**. The absolute filter (go to cash when negative)
   removes winning positions during bull markets, reducing Sharpe.

2. **Longer lookbacks help cross-sectional** (252d: 0.997 vs 63d: 0.662). Momentum
   is stronger at longer horizons.

3. **B&H remains unbeatable** in this period (2015-2025). The bull market makes active
   strategies face a high hurdle.

4. **Monthly rebalancing is crucial**. L1 daily rebalancing generated 5519 trades
   vs L2's 143. Cost drag per trade matters more than signal quality.

## Script

`scripts/L2_dual_momentum.py` — outputs to `checkpoints/l2_dual_momentum/L2_dual_momentum_results.json`

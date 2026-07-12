# M11i Per-Coin Attribution — Edge Concentration Analysis

**Date**: 2026-05-13 (Cycle 30, Track 2)
**Purpose**: Decompose M11h/i verdict by coin. Is the HAR+Kelly edge concentrated in 1-2 coins or distributed across all 7?

## Concentration Verdict: MODERATE (4/7 coins)

Edge is stable at 4/7 coins across all cap levels. BTC, XRP, ADA, DOT are consistent winners. ETH and SOL are consistent losers. LTC is marginal.

## Per-Coin Summary (fee=100bps)

### cap=1.0 (Calmar-optimal)

| Coin | Win Rate | p-value | Med Delta Sharpe | Med Calmar | Med DD |
|------|----------|---------|------------------|------------|--------|
| BTC-USD | 15/15 (100%) | 0.000 | +0.044 | +0.93 | 54.5% |
| ETH-USD | 0/15 (0%) | 1.000 | -0.245 | +0.63 | 70.6% |
| SOL-USD | 3/15 (20%) | 0.996 | -0.423 | -1.41 | 62.9% |
| LTC-USD | 6/15 (40%) | 0.849 | -0.195 | -0.46 | 59.8% |
| XRP-USD | 15/15 (100%) | 0.000 | +0.296 | +1.44 | 55.7% |
| ADA-USD | 12/15 (80%) | 0.018 | +0.280 | -0.01 | 59.8% |
| DOT-USD | 15/15 (100%) | 0.000 | +0.643 | -0.35 | 64.0% |

### cap=3.0 (DD-penalized)

| Coin | Win Rate | p-value | Med Delta Sharpe | Med Calmar | Med DD |
|------|----------|---------|------------------|------------|--------|
| BTC-USD | 15/15 (100%) | 0.000 | +0.061 | +0.57 | 90.2% |
| ETH-USD | 0/15 (0%) | 1.000 | -0.345 | +0.29 | 99.1% |
| SOL-USD | 3/15 (20%) | 0.996 | -0.509 | -1.01 | 92.0% |
| LTC-USD | 6/15 (40%) | 0.849 | -0.078 | -0.24 | 89.8% |
| XRP-USD | 15/15 (100%) | 0.000 | +0.477 | +1.28 | 82.3% |
| ADA-USD | 15/15 (100%) | 0.000 | +0.460 | +0.20 | 89.7% |
| DOT-USD | 15/15 (100%) | 0.000 | +0.612 | -0.14 | 91.9% |

## Cross-Cap Delta (cap=3.0 minus cap=1.0)

| Coin | Delta Win Rate | Delta Sharpe | DD Mult | Calmar Delta |
|------|---------------|--------------|---------|--------------|
| BTC-USD | +0% | +0.017 | 1.66x | -0.36 |
| ETH-USD | +0% | -0.100 | 1.40x | -0.34 |
| SOL-USD | +0% | -0.086 | 1.46x | +0.40 |
| LTC-USD | +0% | +0.117 | 1.50x | +0.23 |
| XRP-USD | +0% | +0.180 | 1.48x | -0.16 |
| ADA-USD | +20% | +0.180 | 1.50x | +0.20 |
| DOT-USD | +0% | -0.031 | 1.44x | +0.21 |

Key: ADA-USD is the only coin that improves win rate with cap=3.0 (80% → 100%). All coins see ~1.5x DD multiplier.

## Per-Horizon Patterns

Winning coins (BTC, XRP, ADA, DOT) show edge at ALL horizons (h=1, 5, 10, 15, 20). Losing coins (ETH, SOL) show edge at h=20 only. LTC is marginal with edge only at h=15, h=20.

## Implications for M_NEXT_VOL Roadmap

1. **Coin selection matters**: Strategy should exclude ETH-USD and SOL-USD. These coins have negative delta-Sharpe at all caps — HAR+Kelly actively hurts.

2. **Horizon flexibility**: For winning coins, edge is present at all horizons. No need to specialize on short vs long horizon.

3. **Calmar-optimal = cap=1.0**: Even for winning coins, the DD penalty from higher caps outweighs the Sharpe gain. XRP-USD at cap=1.0 has Calmar +1.44 (best in class).

4. **ADA-USD benefits from cap relaxation**: Only coin where cap=3.0 improves win rate. ADA has lower volatility, so higher Kelly fractions are less penalized by DD.

5. **ETH is structurally hostile**: Highest crypto kurtosis (~50), consistent negative delta-Sharpe. Confirm M10 RG finding — ETH is the hardest coin for volatility models.

## Files

- `scripts/m11i_per_coin_attribution.py`: Attribution script
- `results/m11i_per_coin/m11i_per_coin_attribution.csv`: Full per-coin data
- `results/m11i_per_coin/results.json`: JSON with all metrics

# M15: Log-LSTM RV

**Model:** LSTM (Hochreiter & Schmidhuber 1997) applied to log-realized variance.
**Date:** 2026-05-14
**Updated:** 2026-08-17 — hidden=32 re-run §C (issue #11395): **NO BEATS**, claim "deployable" retracted.
**Script:** `scripts/m15_lstm_rv.py`

## Architecture

```
Input:  sliding window W=22 days x 3 features [log(RV), returns, sign(returns)]
Model:  LSTM(hidden=H, 1 layer) + FC(H, 1)
Target: log(RV_{t+h}), h in {1, 5, 10}
Loss:   MSE on log-RV
Decode: exp(pred) -> RV level, then log(RV) for Kelly comparison
```

Three capacities were tested historically:
- **hidden=128**: ~68,225 params -- NO BEATS (historical run, not tracked)
- **hidden=64**: ~17,729 params -- NO BEATS (tracked runs: `m15_lstm_rv_btc_sc`, BTC only)
- **hidden=32**: ~4,769 params -- historical "BEATS" **invalidated by the §C test** (NO BEATS)

## Methodology

- Walk-forward 5-fold expanding window, refit every 22 days
- Early stopping (patience=10, max epochs=100)
- Expanding normalization (mean/std from training fold only)
- 7 coins (BTC, ETH, SOL, LTC, XRP, ADA, DOT) x 3 horizons (h=1,5,10) x 4 seeds (0,1,7,42) = 84 combos
- Kelly cap=1.0, fee=50bps, mu_window=60
- Sign-test: binomial one-sided (historical gate, NOT the §C gate)
- **§C gate (issue #11395):** conjunction edge >= 2σ cross-seed **AND** dm_p_median < 0.05 on the **precision loss** (loss_fn="mse"), plus dominance guard

## Results: hidden=32 (~4.8K params) -- §C re-run (issue #11395)

**VERDICT: NO BEATS** (44/84, p=0.372, win_rate=52.4%)

| Metric | Value |
|--------|-------|
| LSTM beats HAR | 44/84 (52.4%) |
| p-value (sign-test) | 0.3718 |
| Median delta-Sharpe (LSTM - HAR) | +0.0029 |
| Median MSE change | +11.2% (LSTM worse) |
| Runtime | 4.5h (16036s, GPU) |
| Results file | `scripts/results/m15_lstm_rv_h32/results.json` (tracked) |

### §C conjunction per horizon (loss = mse)

| Horizon | edge (MSE) | σ cross-seed | dm_p_median | beaten | Verdict §C |
|---------|------------|--------------|-------------|--------|------------|
| h=1 | -9.1% | 6.50 | 0.027 | 18/28 | NO BEATS |
| h=5 | -9.0% | 11.43 | 0.083 | 7/28 | NO BEATS |
| h=10 | -10.9% | 15.41 | 0.112 | 7/28 | NO BEATS |

The Diebold-Mariano test is significant at h=1 (p=0.027) but **in the direction LSTM worse**: the
HAR baseline is significantly more precise at the short horizon. A significant p-value is not a
BEATS -- the sign of the edge decides.

### Per-coin results (hidden=32, §C run)

| Coin | Median delta-Sharpe | MSE change | Beats |
|------|-------------------|------------|-------|
| BTC-USD | +0.0123 | -11.9% | 12/12 |
| ETH-USD | -0.0286 | +8.3% | 4/12 |
| SOL-USD | +0.0131 | +17.1% | 9/12 |
| LTC-USD | -0.0744 | +14.9% | 0/12 |
| XRP-USD | +0.0331 | +17.4% | 8/12 |
| ADA-USD | +0.0192 | +9.4% | 7/12 |
| DOT-USD | -0.0530 | +8.7% | 4/12 |

Only BTC shows a median MSE reduction (-11.9%). The historical per-coin claims (DOT 12/12, ADA 11/12,
XRP 9/12) do **not** reproduce on the tracked §C run.

### Per-horizon results (hidden=32, §C run)

| Horizon | Median delta-Sharpe | Beats |
|---------|-------------------|-------|
| h=1 | +0.0123 | 18/28 |
| h=5 | -0.0253 | 13/28 |
| h=10 | -0.0077 | 13/28 |

### Historical run (NOT tracked, claims only)

The original hidden=32 run (2026-05) claimed BEATS (52/84, p=0.0188, median delta-Sharpe +0.0121,
DOT 12/12, h=1 23/28). These numbers were based on a **sign-test of Kelly Sharpe alone** -- never
validated by the §C conjunction. The run is not tracked; the §C run above is the reproducible
reference and it **infirms** the BEATS.

## Results: hidden=64 and hidden=128 (historical, not tracked)

Historical claims (2026-05, 84-combo runs not tracked in the repo):
- hidden=64: NO BEATS (45/84, p=0.2928)
- hidden=128: NO BEATS (38/84, p=0.8369)

Tracked substitutes: `scripts/results/m15_lstm_rv_btc_sc` (hidden=64, loss_fn="linear") and
`m15_lstm_rv_btc_sc_mse` (hidden=64, loss_fn="mse"), both BTC-only, both **NO BEATS** in their
§C verdict. The historical 84-combo numbers above are **not reproducible** (runs never tracked)
and should not be cited as evidence.

## Capacity comparison (revised)

| Metric | h=32 (§C run) | h=64 (tracked BTC) | h=128 (historical) |
|--------|--------------|--------------------|--------------------|
| Win rate | 52.4% (44/84) | 58.3% / 66.7% (12 BTC combos) | 45.2% (not tracked) |
| Median MSE change | +11.2% | -12.2% / -11.5% | +7.0% (not tracked) |
| Verdict | **NO BEATS** | NO BEATS | NO BEATS |

The historical "monotonic capacity sweep" interpretation (smaller = better, overfitting signature)
is **not supported**: the tracked h=64 BTC runs were actually **more precise** in MSE (-12%) yet
still failed the §C conjunction on significance. The correct reading: at every tracked capacity,
the LSTM fails the §C gate.

## Caveats (G.2 Honesty)

### C.1 -- MSE worse despite Sharpe better

Median MSE change is +11.2% (LSTM worse). The historical BEATS verdict came entirely from Kelly
Sharpe, not forecast accuracy. The §C re-run shows the Sharpe gain (+0.0029) is **indistinguishable
from noise** (p=0.372) -- the MSE paradox is real but the Sharpe side is not statistically significant.

### C.2 -- Weak coins drag

ETH, LTC and DOT show negative median delta-Sharpe on the §C run. The overall Sharpe win rate
(52.4%) is carried by BTC (12/12) and, more weakly, SOL/XRP/ADA.

### C.3 -- No horizon holds the §C conjunction

The edge on the precision loss is negative at all three horizons. h=5 is essentially a coin flip
(13/28, delta-Sharpe -0.0253). No horizon qualifies as an edge.

## Comparison with M-series

| Model | Verdict | Win rate | p-value | Notes |
|-------|---------|----------|---------|-------|
| M2 HAR Classic | **Baseline** | -- | -- | Sharpe +0.313 vs BH |
| M10 Realized GARCH | NO BEATS | -- | -- | MSE +62% |
| M12 HAR-RV-J | **BEATS** | -- | p=0.0015 | Jump-augmented, deployed (`HAR-RV-J-Kelly`) |
| M13 MS-HAR | NO BEATS | 39/84 | p=0.7774 | Markov-Switching |
| M14 HEAVY | NO BEATS | 48/84 | p=0.1149 | Bivariate |
| M15 LSTM h=32 | **NO BEATS** | 44/84 | p=0.372 | §C re-run (issue #11395) |
| M15 LSTM h=64 (BTC) | NO BEATS | 7-8/12 | -- | §C tracked runs |

## Conclusion

The historical BEATS of M15 hidden=32 (p=0.0188, "deployable") was based on a sign-test of Kelly
Sharpe only. The §C re-run (issue #11395, DM on the mse precision loss, seeds 0/1/7/42, 84 combos)
**infirms** it: edge negative at all horizons (-9.1% / -9.0% / -10.9%), Sharpe gain not significant
(p=0.372). M15 h=32 is **removed from the KEEPERS** (`RECAP_KEEPERS_V2.md`).

The lesson: a Sharpe gain without a precision gain is **indistinguishable from noise** on 84 combos.
The §C conjunction (edge >= 2σ AND dm_p_median < 0.05 on the precision loss) exists exactly for this
case. A distinct §C-conformant M15 entry exists for BTC-only hidden=64 refit-110 (2/3 BEATS at
h=5/h=10, issue #11034) -- see `REGISTRY.md`; it is a different configuration, not the retracted claim.

Runtime (§C run): h=32 ~4.5h (16036s, RTX 3070 Laptop).

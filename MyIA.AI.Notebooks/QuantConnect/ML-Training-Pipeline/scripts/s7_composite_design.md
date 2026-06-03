# S7 Composite Design — Regime→Vol→Ridge→Gate→Portfolio

Date: 2026-05-16

## 1. Rationale

Individual KEEPERS that BEAT benchmarks:
- **S3 HMM** (delta +0.669, 4/4 seeds): Regime detection bull/bear
- **S4 v2 Ridge** (delta +0.325, 4/4 seeds): Regime-conditional inverse-vol Ridge

Individual stages that FAILED:
- **S2 vol ensemble** (NO BEATS): DM-weighted ensemble didn't improve
- **S5 LASSO stop** (NO BEATS): Stop-loss prediction didn't add value

Hypothesis: combining S3 regime detection + S4 v2 regime-conditional Ridge +
execution gating (skip high-cost trades via cost proxy) yields a composite
that BEATS S4 v2 alone by >= +0.10 delta Sharpe.

Why this combination vs S4 v2 alone:
1. S4 v2 already uses HMM regime — but it applies the SAME Ridge alpha grid
   regardless of market microstructure. The composite adds vol-conditioned
   alpha selection (wider in low-vol, tighter in high-vol).
2. S6 cost-gating filters out regime switches during high-spread periods,
   reducing whipsaw losses (5 switches/year in S3, some are noise).

## 2. Architecture

```
Data (yfinance: SPY/TLT/sectors + VIX)
    |
    v
RegimeDetector (S3 HMM 2-state)
    |→ regime_label: {bull, bear}
    |→ regime_prob: float [0,1]
    |
    v
VolConditioner (HAR-RV-J inline, 22-day horizon)
    |→ vol_regime: {low, normal, high}
    |→ forecast_rv: float
    |
    v
RiskWeights (S4 v2 Ridge regime-conditional)
    |→ raw_weights: dict[symbol, float]
    |→ Adjust alpha based on vol_regime:
    |     low_vol → alpha_low (wider, more aggressive)
    |     high_vol → alpha_high (tighter, more defensive)
    |
    v
ExecutionGate
    |→ cost_estimate: float (ATR-based proxy)
    |→ trailing_avg_cost: float (20-day EMA)
    |→ skip trade if cost_estimate > k * trailing_avg_cost
    |→ k = 1.5 (tuned, no overfit guard)
    |
    v
PortfolioOrders
    |→ final_weights: dict[symbol, float]
    |→ Transaction costs applied
```

## 3. Data Flow

### Inputs (daily, yfinance)
- **Prices**: SPY, TLT, XLF, XLK, XLE, XLV, XLY, XLI, XLB, XLU, XLP
- **Volatility**: ^VIX (level)
- **Period**: 2017-01-01 to 2026-12-31 (OOS 2027 strict)

### Per-Step Pipeline
1. Load prices + compute returns
2. Fit HMM on expanding window (reused S3 logic: MarkovRegression 2-regime)
3. Predict regime for current day (bull/bear)
4. Compute HAR-RV-J forecast (rv_d, rv_w, rv_m + jump component)
5. Classify vol_regime from HAR-RV-J forecast vs rolling median
6. Select Ridge alpha based on (regime, vol_regime) pair
7. Compute inverse-vol Ridge weights for regime-appropriate assets
8. Estimate trade cost from ATR ratio vs trailing average
9. If cost > threshold: skip rebalance, keep previous weights
10. Apply transaction costs (10bps crypto/5bps ETFs, 50bps stress)

## 4. Interfaces (function signatures)

```python
def detect_regime(returns_df, fit_data, refit_every=22) -> tuple[int, float]:
    """Returns (regime_label: 0=bull/1=bear, regime_prob)."""

def forecast_vol_har_rv_j(returns_series, lookback=22) -> tuple[float, str]:
    """Returns (forecast_rv, vol_regime: 'low'/'normal'/'high')."""

def compute_ridge_weights(
    returns_df, regime_label, vol_regime, alphas
) -> dict[str, float]:
    """Returns {symbol: weight}."""

def gate_execution(
    current_weights, new_weights, cost_estimate, trailing_avg_cost, k=1.5
) -> dict[str, float]:
    """Returns final_weights (may skip if cost too high)."""
```

## 5. Why This Should Work (and Why It Might Not)

### Bull case
- S4 v2 already BEATS (+0.325) — composite adds vol-conditioned alpha tuning
  and execution gating on top. Even a small improvement validates.
- S6 POC showed 57.7% skip rate — filtering bad trades should help.

### Bear case
- Adding complexity on top of a working system often degrades it (overfitting,
  parameter proliferation, reduced degrees of freedom).
- HAR-RV-J vol conditioning may be redundant with HMM regime (both capture
  similar market state information).
- Execution gate may skip the exact regime switches that make S3/S4 profitable.

### Mitigation
- Walk-forward with expanding window: no lookahead
- Multi-seed block bootstrap: guard against overfitting to specific periods
- Gate criterion: delta >= +0.10 vs S4 v2 alone (not vs equal-weight)
- Honest verdict: BEATS / NO BEATS / INCONCLUSIVE

## 6. Compute Requirements

- **CPU only** (no GPU): sklearn Ridge, statsmodels MarkovRegression, numpy
- **Memory**: ~500MB for 11 symbols × 2355 days × walk-forward folds
- **Time estimate**: ~5-10 min per seed × 4 seeds = 20-40 min total
- **Env**: coursia-ml-training (sklearn, statsmodels, yfinance, numpy, pandas)

## 7. Baseline Comparison

Primary baseline: **S4 v2 alone** (Ridge regime-conditional, delta +0.325 vs EqW).
The composite must beat this by >= +0.10 delta Sharpe cross-seed 4/4.

Secondary baseline: **Equal-weight** (all 11 symbols, rebalanced monthly).

Gate: composite_delta_vs_s4v2 >= +0.10 AND t >= 2.0 AND >= 3/4 seeds positive.

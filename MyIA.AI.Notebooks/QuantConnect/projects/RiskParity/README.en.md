# RiskParity Strategy

**Status**: ⚠️ PLAFOND STRUCTUREL CONFIRMÉ - Counter-Example for Educational Purposes

## Performance

| Metric | Value |
|--------|-------|
| Sharpe Ratio | **0.399** |
| CAGR | 7.8% |
| Max Drawdown | 20.9% |
| Period | 2015-2026 |

## Refused buy, re-sent at the next session

The figures in this section come from the QC Cloud backtest of `main.py`; the Performance table above is a separate computation.

At daily resolution every order goes out as `MarketOnClose`: submitted at 10:00 New York time, filled at the close. Lean checks the buying power of a buy before any sell of the same rebalance has filled, and charges it the margin of the buys already accepted that day. On 2015-02-02 the portfolio leaves a 100% BND position: the SPY and GLD buys go through, the TLT buy is refused (status `Invalid`) for a margin shortfall of 110 dollars, and it was never re-sent. The TLT line stayed empty until the March rebalance.

`main.py` now re-sends a refused buy at the next session: `on_order_event` records the refusal, a daily event calls `set_holdings` towards the last rebalance target, and each re-send writes a `RETRY` log line. Before/after measurement, under a protocol posted before the runs (#20523):

| Window | Refused buys | Re-sent and filled | Sharpe | Compounded annual return | Max drawdown |
|---|---|---|---|---|---|
| 2015-01-01 -> 2024-12-31 (coded) | 1 before, 1 after | 0 before, 1 after (TLT, 2015-02-03) | 0.373 -> 0.360 | 7.45% -> 7.29% | 18.4% -> 18.4% |
| 2025-01-01 -> 2026-07-10 (out of sample) | none | — | 0.643, unchanged | 15.08%, unchanged | 10.9%, unchanged |

Out of sample, with no refusal, the fix changes no order. On the coded window the gap comes from February 2015 alone and carries no sign worth keeping. What the fix brings is a backtest that measures the strategy as described.

## Parameters

| Parameter | Values | Default | Role |
|---|---|---|---|
| `mode` | `strategy`, `spy`, `6040` | `strategy` | `strategy` keeps the code's decision; `spy` holds SPY at 100%; `6040` holds SPY at 60% and BND at 40%, rebalanced at the start of each month, one minute after the open |
| `start_date` | date `%Y%m%d` | 2015-01-01 | start of the window |
| `end_date` | date `%Y%m%d` | 2024-12-31 | end of the window |

All three modes trace the portfolio value at each SPY open (chart `shadow`, series `e0` to `e4`). In reference mode, the strategy rebalance and the re-send of refused buys do nothing. Without parameters the strategy's decision is unchanged: the control below checks it order by order.

## Verdict against held references (#21420)

The protocol was written in #21420 before the first backtest, on the model of #21329. For a risk-parity portfolio the 60/40 is the natural reference; SPY held sets the `NO BEATS` threshold. Both references run inside the same algorithm as the strategy, under the same brokerage model and with the same 280-day warm-up.

The compared series are the portfolio value at each SPY open. The tests go through `Paradox46Benchmarks/significance.py`, with a zero risk-free rate:

- Ledoit-Wolf Sharpe difference;
- stationary bootstrap;
- Newey-West difference of means.

On each window, the Holm correction covers the six p-values.

Verdict rule, written before the measurement:

- `BEATS`: positive Sharpe difference, significant (Holm < 0.05) against both references;
- `NO BEATS`: strategy Sharpe below that of SPY held;
- `INCONCLUSIVE`: every other case.

**Harmlessness control: held.** In `strategy` mode, on the coded window, the instrumented code (project 38101154) reproduces the backtest of the original code (`6f35c6d89be8a9fd8525acacd14c4a6b`, project 38101150):

- 438 orders out of 438, with no difference in date, symbol or quantity;
- 27 QC statistics out of 27.

The strategy's orders are submitted at 10:00 New York time and filled at the close, on both windows; none is placed at midnight.

| Window | Sessions | Strategy Sharpe (zero rate) | SPY held (zero rate) | 60/40 (zero rate) | Holm p (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| Coded, 2015-01-02 → 2024-12-31 | 2516 | 0.710 | 0.786 | 0.802 | 1.0 / 1.0 | **NO BEATS** |
| Out of sample, 2025-01-02 → 2026-07-21 | 387 | 1.230 | 1.034 | 1.158 | 1.0 / 1.0 | **INCONCLUSIVE** |

QC statistics (computed by QC with its own risk-free rate). Their Sharpe ratios do not compare with those of the table above: QC subtracts a non-zero risk-free rate and starts from its own daily series, whereas the protocol uses a zero rate on the portfolio value at the open. The ranking of the portfolios can therefore change from one table to the other, and the verdict is read on the table above.

| Window | Mode | QC Sharpe (QC's rate, different scale) | CAGR | Max drawdown | Orders | Backtest |
|---|---|---|---|---|---|---|
| Coded | strategy | 0.360 | 7.29% | 18.4% | 438 | `5475762624cf4a91e21c1e6a6cf24f98` |
| Coded | SPY held | 0.533 | 12.97% | 33.7% | 1 | `626f0da67dc03f843c7a48f1eba06a5e` |
| Coded | 60/40 | 0.442 | 8.41% | 21.7% | 201 | `68a3e2b47da02e8dc69f2a6f053ca650` |
| Out of sample | strategy | 0.721 | 16.26% | 10.9% | 80 | `fdcf4ba6a6258b501ab14f079f267862` |
| Out of sample | SPY held | 0.651 | 18.49% | 18.7% | 2 | `2497915228110d7587d702ca01caf3d7` |
| Out of sample | 60/40 | 0.554 | 12.80% | 11.2% | 30 | `52ff8a147efaeb9be1dd305382824769` |

The out-of-sample backtest was requested up to 2026-10-19 but stops on 2026-07-21: the QC nodes used cut backtests about 90 days before the current date. No parameter was tuned on that period.

**Reading.** On the coded window the strategy is below both references in Sharpe. Against the 60/40, at almost the same annual volatility (8.9% against 9.0%), it returns less per year for a slightly smaller max drawdown. Out of sample its Sharpe is the highest of the three, with no significant difference: over 387 sessions, the 95% bootstrap interval of the difference against SPY held runs from −1.27 to +1.57. Its mean daily return stays below that of SPY held there; its lower volatility carries the Sharpe. The current code therefore beats neither reference measurably, and falls below SPY held on its own window.

## Why This Strategy Hit a Ceiling

### Root Cause: Anti-Pattern in Bull Markets

Risk parity allocates capital inversely proportional to volatility:
- **Hypothesis**: Equal risk contribution = better risk-adjusted returns
- **Reality (2015-2026)**: Underperforms simpler approaches

### What Was Tested (and Failed)

| Iteration | Modification | Result | Why It Failed |
|-----------|--------------|--------|---------------|
| H5 | Replace TLT with IEF | Sharpe 0.330 | TLT superior in bull bond market (2015-2020) |
| H6 | Vol targeting 10% | Negative | Cash drag in low-vol (anti-pattern in bull) |
| H7 | VIX filter >25 (exit to cash) | Negative | Too little time in stress (<15%) = cash drag |

### Why Risk Parity Underperforms (2015-2026)

**The bull market problem**:
1. **Vol targeting reduces exposure**: When vol is low, strategy reduces exposure (misses gains)
2. **Bonds underperformed post-2020**: IEF/TLT correlation with equities during rate hikes
3. **Equal risk ≠ equal return**: Low-vol assets (bonds) drag down returns in bull markets
4. **Complexity without benefit**: Simple equal-weight outperforms

### Comparison to Alternatives

| Strategy | Sharpe | CAGR | Complexity |
|----------|--------|------|------------|
| RiskParity | 0.399 | 7.8% | High (vol weighting, rebalancing) |
| Equal Weight (60/40) | ~0.45 | ~9% | Low |
| AdaptiveAssetAllocation | 0.518 | 8.0% | High (momentum + min-var) |

### The "Vol Targeting" Anti-Pattern

Risk parity often uses vol targeting (e.g., target 10% vol):
- **In low-vol periods**: Reduce exposure to maintain target → miss gains
- **In high-vol periods**: Increase exposure → buy high, sell low
- **Net result**: Negative alpha in trending markets

**2015-2026 was mostly a bull market**: Vol targeting consistently reduced exposure during the best periods.

### Lessons Learned

1. **Risk parity ≠ free lunch**: Equal risk contribution doesn't guarantee better returns
2. **Vol targeting is regime-dependent**: Works in choppy markets, fails in trending markets
3. **Complexity isn't always better**: Equal-weight 60/40 outperforms with less effort
4. **Bonds aren't always diversifiers**: Post-2020 rate hikes broke the bond/equity correlation
5. **Know when to stop**: After 3 failed iterations (H5-H7), the ceiling is confirmed

## When Risk Parity CAN Work

This approach may work in:
- **Sideways/choppy markets**: Where vol targeting adds value
- **High volatility environments**: Where risk equalization protects capital
- **Multi-asset futures**: Where cointegration creates more stable relationships
- **Regime-aware versions**: That adjust approach based on market state

**For 2015-2026 US equities**: Plafond structurel confirmé.

## Pedagogical Value

This strategy demonstrates:
- ⚠️ The **vol targeting anti-pattern** in bull markets
- ⚠️ **Complexity ≠ performance**: Simple equal-weight can beat sophisticated risk parity
- ⚠️ **Regime dependence**: Strategies optimized for one regime may fail in another
- ⚠️ **When to declare a ceiling**: After 3+ failed iterations with clear hypotheses

## Comparison to Better Alternatives

```python
# RiskParity (volatility-weighted)
weights = 1 / volatility
weights /= weights.sum()

# Equal weight (simpler, better 2015-2026)
weights = np.array([1/n] * n)

# Adaptive (momentum + min-var)
# See AdaptiveAssetAllocation project
```

## References

- **AdaptiveAssetAllocation**: Combines momentum + min-var (Sharpe 0.518)
- **AllWeather**: Simpler multi-asset portfolio (Sharpe 0.667)
- **OPTIMIZATION_BACKLOG.md**: Full iteration history (H5-H7)

---

**Note**: This strategy is kept as a counter-example. For production use, consider simpler approaches (equal weight) or momentum-based alternatives (AdaptiveAssetAllocation).

# TrendFilteredMeanReversion Strategy

**Status**: ❌ PLAFOND STRUCTUREL CONFIRMÉ - Counter-Example for Educational Purposes

## Performance

| Metric | Value |
|--------|-------|
| Sharpe Ratio | **-0.016** |
| CAGR | 3.4% |
| Max Drawdown | 11.4% |
| Period | 2015-2026 |

## Why This Strategy Failed

### Root Cause: Signal Frequency vs. Quality Trade-off

This strategy combines:
1. **RSI(2) < 10**: Extreme oversold signal (pullback)
2. **SMA200 filter**: Only trade in bull markets
3. **Time stop 5 days**: Exit if signal doesn't materialize

**The problem**: It's a **valid signal** (73% win rate) but occurs **too rarely** (~9 trades/year).

### Performance Breakdown

| Version | Signal | Sharpe | Trades/Year | Win Rate | Max DD |
|---------|--------|--------|-------------|----------|--------|
| v1.0 | RSI(2) < 10 | -0.016 | ~9 | 73% | 11.4% |
| v2.0 | RSI(2) < 20 | -0.002 | ~31 | 71% | 16.2% |
| v3.0 | RSI(3) < 15 | -0.050 | ~12 | 72% | 10.3% |
| v4.0 | Multi-instrument (3x) | -0.129 | ~27 | 65% | 18.5% |

**Pattern observed**:
- **Tighter signal** (RSI<10) = High quality but too rare
- **Looser signal** (RSI<20) = More frequent but lower quality
- **Multi-instrument** = More trades but dilutes edge + higher correlation risk

### Cause of Failure: Cash Drag

| Metric | Value |
|--------|-------|
| Time in cash | ~85% |
| Cash return (2015-2026) | ~0% (no interest earned) |
| Risk-free rate (T-bills) | 2-5% annualized |

**The structural problem**:
- Strategy is in cash 85% of the time
- Cash earns 0% while risk-free (T-bills) earns 2-5%
- This **opportunity cost** creates negative alpha
- Even with 73% win rate, the cash drag destroys returns

### Why Multi-Instrument Failed (v4.0)

We tested SPY + QQQ + IWM to increase opportunities:
- **Hypothesis**: 3x more instruments = 3x more signals
- **Reality**: Signals are correlated (all 3 trigger together) + individual quality drops
- **Result**: Sharpe -0.129 (worse than baseline)

### Lessons Learned

1. **Signal quality vs. frequency is a real trade-off**: Can't have both
2. **Cash drag is real**: Being in cash 85% of the time = -2 to -5% annualized vs. T-bills
3. **Multi-instrument ≠ independent signals**: Correlated markets don't increase true opportunities
4. **Know when to stop**: We tested RSI(2), RSI(3), RSI(7), multi-instrument - all failed
5. **Regime dependence**: This strategy only works in bull markets with sharp pullbacks (rare)

## When This Approach CAN Work

Similar strategies may work in:
- **Bear markets**: RSI pullbacks are more frequent
- **Higher volatility**: More extreme RSI readings
- **Individual stock screening**: Cherry-pick the best setups (not systematic)
- **Different asset classes**: Crypto, FX where mean reversion is stronger

**For SPY (2015-2026)**: Plafond structurel confirmé.

## Pedagogical Value

This strategy demonstrates:
- ❌ The importance of **signal frequency** in strategy design
- ❌ **Cash drag** as a hidden cost (especially vs. risk-free rate)
- ❌ When to declare a **plafond structurel** (after exhaustive testing)
- ❌ The **73% win rate trap**: High win rate ≠ profitability if trades are too rare

## References

- **OPTIMIZATION_BACKLOG.md**: Full iteration history (v1.0-v4.0)
- **MeanReversion**: Similar strategy but with different parameters

---

**Note**: This strategy has a valid signal but is structurally unprofitable due to cash drag. It serves as a lesson in opportunity cost and signal frequency.

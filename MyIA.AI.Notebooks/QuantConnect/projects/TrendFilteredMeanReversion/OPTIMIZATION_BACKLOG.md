# TrendFilteredMeanReversion - Optimization Backlog

**Cloud Project ID**: 28817422
**Strategy**: Trend-Filtered Mean Reversion (SPY RSI(2) pullback in bull regime)
**Current best**: v1.0 - Sharpe -0.016, CAGR 3.4%, MaxDD 11.4%

---

## Iteration History

### v1.0 - Baseline (2026-03-09)
- **Config**: RSI(2) < 10, SMA200 bull filter, SMA5 exit OR RSI>70 OR 5-day time stop
- **Result**: Sharpe -0.016, CAGR 3.4%, MaxDD 11.4%, ~9 trades/year, Win Rate 73%
- **Status**: BASELINE

### v2.0 - RSI(2)<20 (2026-03-09) - REVERTED
- **Hypothesis**: Relax RSI threshold from <10 to <20 to increase trade frequency
- **Result**: Sharpe -0.002, CAGR 3.4%, MaxDD 16.2%, ~31 trades/year, Win Rate 71%
- **Verdict**: REJECTED - MaxDD 16.2% (worse than v1.0 11.4%). Sharpe marginally better
  but still negative. Too many mediocre entries dilute the signal quality.

### v3.0 - RSI(3)<15 (2026-03-09) - REVERTED
- **Hypothesis**: RSI(3) is smoother than RSI(2), <15 threshold is a middle ground
- **Result**: Sharpe -0.050, CAGR 3.2%, MaxDD 10.3%, ~12 trades/year, Win Rate 72%
- **Verdict**: REJECTED - Sharpe worse than both v1.0 and v2.0. Frequency only marginally
  better than v1.0 (~12 vs 9/year). MaxDD slightly better (10.3% vs 11.4%) but not enough.

---

## Root Cause Analysis

**The fundamental problem**: The strategy spends ~85% of time in cash during the
2015-2026 bull market (SPY > SMA200 most of the time, but RSI(2)<10 is rare).
- Cash at 0% vs risk-free rate ~2-5% = Sharpe penalty even with positive CAGR
- The 73% win rate and 3.4% CAGR confirm the signal IS valid
- But holding 85% cash while market goes up = negative alpha vs buy-and-hold

**Why adjusting RSI threshold alone doesn't fix it**:
- RSI(2)<10: too selective (9 trades/yr), cash drag dominates
- RSI(2)<20: more trades (31/yr) but lower quality, MaxDD spikes, still negative Sharpe
- RSI(3)<15: middle ground but still only 12 trades/yr, RSI(3) less extreme than RSI(2)

---

## Pending Hypotheses

- [ ] **H4 - Multi-instrument RSI(2)<10**: Add QQQ + IWM alongside SPY.
  Each instrument has independent RSI signals -> 3x more opportunities without
  relaxing quality. Each position sized at 33%. This is the RIGHT way to increase
  frequency: more instruments, not lower threshold.
  Expected: ~25-30 trades/year, maintain ~70% win rate, MaxDD ~15%

- [ ] **H5 - Extend to bear market (remove SMA200 filter)**:
  Test without the SMA200 bull filter to see if mean reversion works in bear too.
  Risk: RSI(2)<10 in bear = catching falling knives. Likely worse.

- [ ] **H6 - Shorter time stop (3 days)**:
  Current 5-day time stop may hold positions too long. Try 3-day time stop.
  RSI(2) strategies typically recover within 2-3 days.

- [ ] **H7 - RSI(2)<10 with SMA10 exit (faster)**:
  Replace SMA5 exit with SMA10 to let winners run longer.
  Counter-hypothesis: SMA5 may be cutting winners too early.

- [ ] **H8 - Multiple RSI(2)<10 re-entries (pyramiding)**:
  If RSI(2) keeps falling after entry, add to position.
  Risky but could improve CAGR on the deepest pullbacks.

---

## Key Lessons

1. **Cash drag is the main enemy**: 85% cash during a bull market = negative Sharpe
   even with positive signal. Solution: more instruments, not lower threshold.

2. **Win rate 73% confirms signal is real**: The edge exists. The problem is frequency.

3. **RSI(2)<20 is over-fishing**: At <20, the signal quality degrades (Win Rate 71%)
   and MaxDD spikes to 16.2%. The <10 threshold captures the best opportunities.

4. **Multi-instrument is the right path** (H4): diversify across correlated but
   independent instruments (SPY, QQQ, IWM) to multiply opportunities without
   diluting quality. Each has its own RSI signal.

5. **Rule from prior strategies**: Increase frequency via more instruments,
   NOT by lowering signal quality thresholds.

# QC Research Notebook Agent - Memory

## Key Learnings

### Notebook Execution Constraints

- **QuantBook API not available locally**: Research notebooks using `QuantBook()` cannot be executed outside QC's cloud environment
- **Solution**: Create standalone Python scripts (`.py`) that can be imported in QC Research Lab
- **Alternative**: Provide clear documentation (`.md`) with code snippets and methodology

### Research Notebook Structure

**Optimal structure for diagnostic research**:

1. **Markdown intro**: Context, problem statement, hypotheses
2. **Setup cell**: Load data with QuantBook
3. **Analysis cells**: One hypothesis per cell (cointegration, half-life, etc.)
4. **Backtest cells**: Vectorized tests with parameter variations
5. **Walk-forward cell**: Out-of-sample validation
6. **Markdown findings**: Synthesis table with hypothesis status
7. **Recommendations cell**: JSON output for implementation

### Common Pairs Trading Issues (Pedagogical)

**Critical bugs to check**:
1. **Z-exit threshold**: Should be 0.0 (mean), not 0.5 (premature exit)
2. **Stop-loss level**: Spread-level (preserves neutrality), NOT per-leg
3. **Half-life ignorance**: Fixed insight duration vs adaptive based on HL
4. **Stability filter**: Exclude pairs with HL > 30d for hourly trading

**Diagnostic metrics**:
- Cointegration p-value (< 0.05)
- Half-life of mean-reversion (< 30 days for hourly)
- Stability over time (rolling cointegration test)
- Walk-forward Sharpe (out-of-sample validation)

### File Deliverables

For research tasks, provide:
1. `.ipynb` - Full notebook with markdown pedagogy
2. `.py` - Standalone script for quick execution
3. `_GUIDE.md` - Summary with problem, fixes, next steps

## Project Context

- **Workspace**: `MyIA.AI.Notebooks/QuantConnect/ESGF-2026/`
- **Examples folder**: Contains 11 strategy examples
- **Research subfolder**: Within each example (e.g., `ETF-Pairs-Trading/research/`)

## Patterns

### Hypothesis testing structure

```python
# H1: Test specific parameter change
baseline_metrics = backtest(param=old_value)
test_metrics = backtest(param=new_value)
improvement = test_metrics['sharpe'] - baseline_metrics['sharpe']

print(f"{'✓ H1 CONFIRMED' if improvement > threshold else '✗ H1 REJECTED'}")
```

### Walk-forward validation pattern

```python
for i in range(train_days, len(data), test_days):
    train = data[i-train_days:i]
    test = data[i:i+test_days]

    # Verify assumption on train
    if not validate_assumption(train):
        continue

    # Test on out-of-sample
    result = backtest(test)
    results.append(result)
```

## Common User Requests

- "Fix strategy with negative Sharpe" → Diagnostic research notebook
- "Test if X improves Y" → Hypothesis-driven notebook
- "Compare approaches A vs B" → Side-by-side backtest cells
- "Validate strategy robustness" → Walk-forward validation

## Tools Reference

- `statsmodels.tsa.stattools.coint` - Engle-Granger cointegration test
- `statsmodels.api.OLS` - Beta estimation and half-life calculation
- Vectorized backtesting preferred over iterative (faster)
- `scipy.stats.norm` - Black-Scholes option pricing (research approximations)
- `yfinance` - Standalone data source when QuantBook unavailable

## Options Strategy Research (Added 2026-02-17)

### Key Challenge: Why Options Can't Be Vectorized-Backtested

Options strategies (Wheel, Iron Condor, etc.) CANNOT use simple vectorized backtests because:
- Option premiums depend on **implied volatility** (not observable historically without full options chains)
- Exact pricing needs Black-Scholes, Greeks, IV skew
- QuantConnect handles this in backtest engine, but **QuantBook doesn't have historical options data**

### Research Approach for Options Strategies

When validating robustness across extended periods:

1. **Regime analysis**: SPY price + realized volatility (proxy for VIX)
2. **Premium estimation**: Black-Scholes with historical vol (approximation)
3. **Worst-case scenarios**: Simulate crash events (COVID Mar 2020, etc.)
4. **Monte Carlo**: 1000+ random entry points for Sharpe distribution

### Standalone Execution Pattern

When QuantBook unavailable locally:
```python
# Use yfinance for data
import yfinance as yf
spy = yf.Ticker("SPY")
spy_data = spy.history(start="2019-01-01", end="2026-02-17", interval="1d")
spy_data.index = spy_data.index.tz_localize(None)  # Fix timezone issues
```

### Black-Scholes Put Premium Estimation

```python
from scipy.stats import norm
def black_scholes_put(S, K, T, r, sigma):
    d1 = (np.log(S/K) + (r + sigma**2/2)*T) / (sigma*np.sqrt(T))
    d2 = d1 - sigma*np.sqrt(T)
    return K*np.exp(-r*T)*norm.cdf(-d2) - S*norm.cdf(-d1)

# 30-DTE, 5% OTM put
premium = black_scholes_put(S=400, K=380, T=30/365, r=0.02, sigma=0.20)
```

### Volatility Regime Classification (SPY)

Using 30-day realized vol as VIX proxy:
- **Low VIX** < 15%: ~45% of time, premium 0.8-1.2% monthly
- **Medium VIX** 15-25%: ~50% of time, premium 1.5-2.5% monthly
- **High VIX** > 25%: ~5% of time, premium 3-6% monthly (high assignment risk)

### Research Completed

**Option-Wheel-Strategy Robustness (2026-02-17)**:
- Extended backtest period from 2020-06 to 2019-01 is SAFE
- COVID crash (Mar 2020) creates -10 to -15% DD, recovers in 12-18 months
- Expected Sharpe: 0.90-1.05 (vs current 0.996)
- Recommendation: `SetStartDate(2019, 1, 1)` with NO parameter changes
- Files: `research_robustness_standalone.ipynb`, `RESEARCH_SUMMARY.md`

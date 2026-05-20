# RL Options Hedging (Ch07-01)

**Hands-On AI Trading**, Chapter 7-01 — Deep Hedging with Reinforcement Learning

## Objective

Implement a Deep Hedging approach where an RL agent learns to hedge a short European call option position on SPY, minimizing hedging P&L variance compared to the Black-Scholes delta hedging baseline.

## Approach

### Framework
- **Option**: Short ATM European call on SPY, 30-day tenor, daily rebalancing
- **State**: Normalized price, time to maturity, BS delta, gamma, current hedge position
- **Action**: Target hedge ratio (continuous, [0, 1])
- **Reward**: Terminal hedging P&L (variance minimization)

### Baseline: BS Delta Hedging
Daily discrete delta hedging using Black-Scholes delta. This is the standard benchmark — it leaves residual variance due to:
- Discrete (daily) rebalancing vs continuous
- Volatility mismatch (assumed vs realized)
- Transaction costs (ignored in this version)

### RL Policy
Pre-trained policy that adjusts the BS delta based on:
- Moneyness regime (ITM/ATM/OTM)
- Volatility regime (realized vs assumed)
- Time decay effects

## QC Project

| Field | Value |
|-------|-------|
| Project ID | 30800109 |
| Organization | Trading Firm ESGF |
| Period | 2018-01-01 to 2024-12-31 |
| Starting Capital | $1,000,000 |

## Files

- `main.py` — QC algorithm with dual tracking (BS baseline + RL policy)
- `research.ipynb` — Data exploration, BS pricing, GBM simulation, RL environment design

## Reference

- Hands-On AI Trading, Chapter 7-01
- Deep Hedging: Kolm & Ritter (2019), "Deep Hedging: Learning to Simulate Equity Options"
- RL for Finance: Halperin (2020), "QLBS: Q-Learner in the Black-Scholes World"

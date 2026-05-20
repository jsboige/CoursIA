# RL-DQN-Trading

**Asset class:** US Equities/ETF (5 ETFs)
**Cloud project ID:** None (local only)

## Description

Deep Q-Network RL agent using MLPRegressor as Q-function approximator on 5 ETFs with risk-adjusted reward function.

## How to Run

**Lean CLI:**


**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | DQN with MLPRegressor |
| Universe | 5 ETFs |
| Reward | Risk-adjusted (drawdown penalty) |

## Files

- main.py - Strategy (v2.0.1, DQN agent)

## References

- Mnih et al. (2015), Human-level control through deep RL

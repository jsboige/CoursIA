# Framework_Composite_TrendWeather

**Asset class:** US Equities (ETF + stocks)
**Cloud project ID:** None (local only)

## Description

Framework composite combining TrendStocks (75%) with AllWeather (25%). Trend uses SMA200+EMA, AllWeather provides diversification.

## How to Run

**Lean CLI:**


**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 1.155 |
| CAGR | 27.4% |
| Max Drawdown | 27.7% |
| Allocation | 75% Trend / 25% AllWeather |

## Files

- main.py - Strategy (v1.5, T75/AW25 composite)

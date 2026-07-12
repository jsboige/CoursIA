Execute iterative improvement workflow for QuantConnect strategies: $ARGUMENTS

Use the `qc-iterative-improve` skill for the detailed workflow.

Usage:
- `/qc-iterative-improve #19` - Work on issue #19 (MeanReversion)
- `/qc-iterative-improve ForexCarry` - By strategy name
- `/qc-iterative-improve #27 --iterations=5` - Custom iteration count
- `/qc-iterative-improve #24 --no-backtest` - Notebook research only

Issue mapping:
- #17 ForexCarry (BROKEN, Sharpe -1.80)
- #18 VIX-TermStructure (BROKEN, Sharpe -0.97)
- #19 MeanReversion (BROKEN, Sharpe -0.042)
- #27 Crypto-MultiCanal (BROKEN, 0 trades)
- #20 FuturesTrend (Sharpe 0.019)
- #21 TurnOfMonth (Sharpe 0.127)
- #22 MomentumStrategy (Sharpe 0.216)
- #23 AllWeather (Sharpe 0.25)
- #24 OptionsIncome (Sharpe 0.288)
- #25 FamaFrench (Sharpe 0.365)
- #26 Sector-Momentum (Sharpe 0.554)

Workflow (research notebook first!):
1. Read issue GitHub + code cloud + last backtests
2. Create/enrich research.ipynb (standalone yfinance+pandas)
3. Explore hypotheses, document verdicts
4. Implement findings in main.py
5. Compile + backtest on QC cloud
6. Evaluate, update issue, iterate if needed

Sub-agent: qc-strategy-improver (model: sonnet)

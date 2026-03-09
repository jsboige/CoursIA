# QC Strategy Analyzer - Agent Memory

## Project Context
- **Working dir**: `d:/CoursIA/MyIA.AI.Notebooks/QuantConnect/projects/`
- **Key docs**: `OPTIMIZATION_BACKLOG.md`, `REGIME_ANALYSIS.md`
- **QC org**: d600793e (personal, PAID - backtests work)

## MCP Tool Patterns

### read_backtest returns very large payloads
- Results saved to `C:\Users\MYIA\.claude\projects\d--CoursIA\<session>\tool-results\*.txt`
- Use Python to extract: `data['backtest']['statistics']` for key metrics
- Use `data['backtest']['rollingWindow']` for regime analysis
  - Keys: `M12_YYYYMMDD` (trailing 12m), `M1_YYYYMMDD` (trailing 1m)
  - Sub-structure: `portfolioStatistics.sharpeRatio`, `.compoundingAnnualReturn`, `.drawdown`, `.totalNetProfit`
- Year-end snapshots: keys matching `M12_*1231`
- Charts: usually only have `name` key, no actual series data for older backtests

### read_backtest_orders returns null for old backtests
- `{"orders":null,"length":null}` for backtests not run recently
- Only works for very recent backtests (within hours)

### list_backtests with includeStatistics=true
- Returns: sharpeRatio, alpha, beta, compoundingAnnualReturn, drawdown, winRate, lossRate, trades

## Regime Analysis Findings (Issue #41, 2026-03-09)

### Annual return patterns by strategy
- **VIX-TermStructure**: Works in VIX compression (2015-17: +82%), fails in tail events and post-2018 SVXY -0.5x restructure (2018-25: -23%)
- **ForexCarry**: Only 2013-14 positive years (pre-T-bill era). Post-2018, T-bills > FX momentum = negative Sharpe structurally
- **TurnOfMonth**: Bear market signal. 2015-26 is 90% bull so Sharpe 0.128. Full-cycle (2000-26) estimated 0.3-0.5
- **OptionsIncome**: Works in low-vol bull (2019, 2021: Sharpe 1.4-1.5), terrible in slow bears (2022: -8.8%). Negative alpha always

### STRUCTURAL_CEILING criteria confirmed
- Alpha persistently negative (all 4 strategies)
- Signal source structurally impaired (SVXY leverage, G10 FX premium post-2008)
- All iterations exhausted (8-11 per strategy, all degraded)

### Key structural events
- **Feb 5, 2018 VIXplosion**: SVXY restructured from -1x to -0.5x (halved roll yield for VIX-TS forever)
- **2008 GFC**: G10 carry premium collapsed, never recovered (ForexCarry ceiling predates backtest)
- **2022 rate hikes**: Worst year for TOM (-6.1%), OptionsIncome (-8.8%), and covered calls generally

## Workflow Notes
- Always extract `portfolioStatistics` from rolling windows (not `tradeStatistics`) for return/Sharpe
- Year-end M12 gives best regime picture: one data point per year = clear annual performance
- M1 monthly data useful for event analysis (VIXplosion Feb 2018, COVID Mar 2020 etc.)

# Piotroski F-Score Quality Value

## Source
- **QC Library**: Strategy #343 - High Book-to-Market High F-Score Quality Value
- **Author**: Louis Szeto
- **Concept**: Systematic equity long-only value + quality screen using Piotroski F-Score anomaly
- **QC Cloud Project**: 29687591 (cloned 2026-04-05)

## Concept
A fundamental value strategy using the Piotroski F-Score (9-point accounting-based scoring system)
to identify financially strong value stocks. The universe selects the top 20% of stocks by
book-to-market ratio (highest value), then filters for F-Score >= 8 (financially healthy).
Equal-weighted portfolio, monthly rebalance.

## Universe
| Component | Selection | Count |
|-----------|-----------|-------|
| Value filter | Top 20% by book-to-market (1/P/B) | ~20% |
| Quality filter | F-Score >= threshold (default 8) | Variable |
| Final cap | Max universe size | 100 |
| Liquidity filter | Price > $1, dollar volume > $100K | - |
| Benchmark | SPY | 1 |

## Piotroski F-Score Components (9 points)

### Profitability (4 points)
| # | Component | Signal |
|---|-----------|--------|
| 1 | ROA > 0 | Positive return on assets |
| 2 | Operating Cash Flow > 0 | Positive cash generation |
| 3 | ROA Change (t > t-1) | Improving profitability |
| 4 | Accruals (CFO/Assets > ROA) | Earnings quality |

### Leverage, Liquidity, Source of Funds (3 points)
| # | Component | Signal |
|---|-----------|--------|
| 5 | Leverage Decreased | Reduced debt burden |
| 6 | Current Ratio Increased | Improved liquidity |
| 7 | No Equity Issuance | No dilution |

### Operating Efficiency (2 points)
| # | Component | Signal |
|---|-----------|--------|
| 8 | Gross Margin Increased | Improving pricing power |
| 9 | Asset Turnover Increased | Better asset utilization |

## Architecture (Alpha Framework)
| Component | Implementation |
|-----------|---------------|
| Universe Selection | PiotroskiScoreUniverseSelectionModel (custom) |
| Alpha Model | ConstantAlphaModel (UP, 30-day) |
| Portfolio Construction | EqualWeightingPortfolioConstructionModel |
| Execution | SpreadExecutionModel (max 1% spread) |
| Risk Management | None (inherent in quality screening) |

## Parameters
- **Score threshold**: 8 (of 9, configurable)
- **Max universe size**: 100 (configurable)
- **Rebalance frequency**: Monthly (month start)
- **Universe resolution**: Hourly
- **Warmup period**: 3 years (fundamental data accumulation)
- **Initial capital**: $10,000,000

## Performance (Author Reported)
- **OOS 1Y Sharpe**: 2.09
- **5Y CAGR**: 18.44%
- **5Y Drawdown**: 24.20%
- **Win Rate**: 62%

## Files
| File | Description |
|------|-------------|
| `main.py` | Algorithm entry point (Alpha Framework) |
| `universe.py` | Custom universe selection with F-Score filtering |
| `symbol_data.py` | Per-symbol fundamental data tracking with RollingWindow |
| `piotroski_score.py` | 9-component F-Score calculation |
| `piotroski_factors.py` | Fundamental data field extraction |

## License
QuantConnect Community Strategy - open source

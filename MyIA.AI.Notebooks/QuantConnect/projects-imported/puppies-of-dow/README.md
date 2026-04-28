# Puppies of the Dow

## Source
- **QC Library**: Dogs/Puppies of the Dow
- **Concept**: Select lowest-priced stocks from highest-yielding Dow components
- **QC Cloud Project**: 29687759 (cloned 2026-04-28)

## Concept
A variant of the classic "Dogs of the Dow" strategy. First selects the 10 Dow components with the highest total yield (dividend + buyback), then picks the 5 with the lowest price. The intuition is that high-yield + low price suggests undervaluation with potential for mean reversion.

## Universe
| Filter | Criteria |
|--------|----------|
| Base universe | Dow Jones Industrial Average (via DIA ETF holdings) |
| Price filter | > $5 |
| Yield filter | Total yield > 0 |
| Dogs | Top 10 by total yield |
| Puppies | Top 5 lowest-priced from Dogs |

## Parameters
- **Portfolio size**: 5 stocks
- **Weighting**: Equal weight (20% each)
- **Rebalance**: Annual (year start)
- **Warmup**: 365 days

## Backtest Results (12-year)
See `research.ipynb` for detailed analysis.

## License
QuantConnect Community Strategy - open source

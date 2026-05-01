# Commodity Term Structure

## Source
- **QC Library**: Strategy #26 - Term Structure Effect in Commodities
- **Quantpedia**: Strategy #22
- **Concept**: Long-short commodity futures based on roll returns (backwardation/contango)
- **QC Cloud Project**: 29688398 (cloned 2026-04-05)

## Concept
A commodity futures strategy exploiting the term structure effect. Calculates annualized roll returns
from near vs distant contract price ratios. Long the top quintile in backwardation (positive roll return)
and short the top quintile in contango (negative roll return). Monthly rebalance, equal-weighted.

## Universe
| Component | Selection | Count |
|-----------|-----------|-------|
| Softs | Cocoa, Coffee, Cotton, Orange Juice, Sugar | 5 |
| Grains | Corn, Oats, Soybean Meal, Soybean Oil, Soybeans, Wheat | 6 |
| Meats | Feeder Cattle, Lean Hogs, Live Cattle | 3 |
| Energies | Crude Oil WTI, Heating Oil, Natural Gas, Gasoline | 4 |
| Metals | Gold, Palladium, Silver | 3 |
| **Total** | | **21** |
| Filter | Near + distant contract (0-90 day expiry range) | - |
| Selection | Top quintile backwardation (long) + top quintile contango (short) | ~4+4 |

## Roll Return Calculation
```
R = (ln(P_near) - ln(P_distant)) * 365 / (T_distant - T_near)
```
- **Positive roll return** = backwardation (near > distant) → long signal
- **Negative roll return** = contango (near < distant) → short signal
- **Annualized** by dividing by days-to-expiry difference

## Parameters
- **Initial capital**: $1,000,000
- **Futures filter**: 0-90 days expiry range
- **Rebalance frequency**: Monthly (month start, 30 min after market open)
- **Position sizing**: 10% gross exposure per side, divided equally
- **Quintile size**: floor(N/5) where N = number of commodities with valid roll returns
- **Seed initial prices**: True (for backtesting)
- **Backtest period**: 15 years

## Performance (Author Reported)
- **OOS 5Y CAGR**: -15.71% (long-term)
- **OOS 5Y Drawdown**: 80.80%
- **OOS 5Y Sharpe**: -0.041
- **Recent 3M Return**: 38.85%
- **Recent 1Y Sharpe**: 1.49
- **Recent 3M Sharpe**: 10.52

## License
QuantConnect Community Strategy - open source

# Defensive ETF Rotation (Conditional Sector Rotation)

## Source
- **QC Library**: Conditional Sector Rotation
- **Concept**: RSI-based conditional rotation among equity, leveraged, and inverse ETFs
- **QC Cloud Project**: 29687520 (cloned 2026-04-28)

## Concept
Uses a regime filter (SPY vs 200-SMA) to switch between bull and bear allocation logic. Within each regime, nested RSI conditions select from 9 ETFs including 3x leveraged and inverse products. Concentrated 100% single-position allocation with daily signal evaluation.

## Universe
| Ticker | Type | Role |
|--------|------|------|
| SPY | US Equities | Core equity / regime signal |
| QQQ | Nasdaq-100 | Tech equity / RSI signal |
| TQQQ | 3x Leveraged Nasdaq | Bull regime target |
| UVXY | Volatility (VIX) | Overbought hedge / bear target |
| TECL | 3x Leveraged Tech | Oversold bounce |
| SPXL | 3x Leveraged S&P | Deep oversold recovery |
| SQQQ | 3x Inverse Nasdaq | RSI signal input |
| TECS | 3x Inverse Tech | Bear regime target |
| BSV | Short-term Bonds | Defensive fallback |

## Signal Logic
### Bull regime (SPY > 200-SMA)
1. QQQ RSI > 81 -> UVXY (volatility hedge)
2. SPY RSI > 80 -> UVXY (volatility hedge)
3. Default -> TQQQ (leveraged long)

### Bear regime (SPY < 200-SMA)
1. TQQQ RSI < 30 -> TECL (oversold tech bounce)
2. SPY RSI < 30 -> SPXL (oversold S&P bounce)
3. UVXY RSI > 84 + QQQ above 20-SMA + SQQQ RSI < 31 -> TECS
4. UVXY RSI > 84 + QQQ above 20-SMA -> TECL
5. UVXY RSI > 84 + QQQ below 20-SMA -> max RSI(TECS, BSV)
6. UVXY RSI > 74-84 -> UVXY
7. TQQQ above 20-SMA + SQQQ RSI < 34 -> TECS
8. TQQQ above 20-SMA -> TECL
9. Default -> max RSI(TECS, BSV)

## Parameters
- **RSI period**: 10 days (configurable)
- **SPY SMA**: 200 days (regime filter)
- **QQQ SMA**: 20 days (trend filter)
- **TQQQ SMA**: 20 days (trend filter)
- **Position sizing**: 100% concentrated
- **Signal check**: Daily (OnData)

## Backtest Results (14-year, 2011-2025)
See `research.ipynb` for detailed analysis.

## License
QuantConnect Community Strategy - open source

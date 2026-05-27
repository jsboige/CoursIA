# ESGF-Option-Wheel

**Asset class:** Equities + Options (SPY)

**Cloud project ID:** 29687004

## Description

Wheel Strategy on SPY -- continuously sell OTM cash-secured puts. If assigned, sell OTM covered calls until called away. Generates option premiums while the underlying tends to appreciate.

Risk management: VIX > 20 filter, 21 DTE, 5% OTM strike, max 80% capital exposure. Cash account (IBKR).

## How to Run

### QC Cloud
Open cloud project 29687004, compile and run a backtest. Note: option backtests take ~2-5 minutes.

## Backtest Metrics

| Variant | Sharpe | CAGR | Max DD | Trades |
|---------|--------|------|--------|--------|
| Wheel + VIX filter | **0.569** | 12.9% | 26.4% | 235 |

## Files

| File | Description |
|------|-------------|
| `main.py` | Options wheel strategy with VIX filter and capital management |

## References

- [QuantConnect Options Documentation](https://www.quantconnect.com/docs/v2/writing-algorithms/trading-and-orders/option-strategies)
- Wheel Strategy: theta-positive income generation via systematic put selling

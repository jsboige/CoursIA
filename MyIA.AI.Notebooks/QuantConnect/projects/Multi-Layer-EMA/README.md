# Multi-Layer-EMA

**Asset class:** Crypto (BTCUSDT, ETHUSDT, LTCUSDT on Binance)
**Resolution:** Daily
**Cloud project ID:** 28433748

## Description

Multi-indicator crypto strategy combining EMA trend, RSI, Bollinger Bands, and ATR volatility filter. Entry requires EMA(fast/slow) crossover confirmed by RSI and Bollinger conditions, with ATR-based volatility gating (skip trading when BTC volatility exceeds 60%).

**Note:** Despite the directory name, this strategy is NOT a simple multi-layer EMA alignment on US equities. It is a comprehensive crypto strategy with multiple technical indicators.

## Strategy Logic

| Component | Parameters | Role |
|-----------|------------|------|
| EMA crossover | Fast 10 / Slow 50 (daily) | Trend direction |
| RSI | 14-period Wilders | Overbought/oversold filter |
| Bollinger Bands | 20-period, 2σ | Mean reversion context |
| ATR volatility filter | 14-period, 60% threshold (annualized daily) | Skip high-vol regimes |
| Trailing stop | 92% | Lock profits |
| Fixed stop | 88% | Capital protection |
| Take profit | 125% | Exit target |

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Multi-Layer-EMA"`

**QC Cloud:** Deployed as project 28433748.

## Backtest Metrics

Verified on QC Cloud (project 28433748, 2018-01-01 to 2024-12-31):

| Metric | Value |
|--------|-------|
| Sharpe | 0.798 |
| CAGR | 24.99% |
| Max Drawdown | 57.1% |
| Orders | 196 |

| Configuration | Value |
|---------------|-------|
| Assets | BTCUSDT, ETHUSDT, LTCUSDT (Binance) |
| Resolution | Daily |
| Max positions | 3 |
| Stop loss | Trailing 92%, Fixed 88% |
| Take profit | 125% |

> **Note:** The trade count above comes from the QC Cloud web UI (*Backtests Results* treegrid, "Orders" column). The `read_backtest` MCP method does not parse the `totalOrders` field (always reports 0), which previously led to a false "0 trades" diagnostic. Orders fill correctly — verified by a 31.5% drawdown on a forced 50% BTC position mirroring the 63% COVID crash.

## Files

- main.py - Strategy (OptimizedCryptoAlgorithm class)

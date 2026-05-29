# Multi-Layer-EMA

**Asset class:** Crypto (BTCUSD, ETHUSD, LTCUSD on Coinbase)
**Resolution:** Hourly
**Cloud project ID:** 28433748

## Description

Multi-indicator crypto strategy combining EMA trend, RSI, Bollinger Bands, and ATR volatility filter. Entry requires EMA(fast/slow) crossover confirmed by RSI and Bollinger conditions, with ATR-based volatility gating (skip trading when BTC volatility exceeds 60%).

**Note:** Despite the directory name, this strategy is NOT a simple multi-layer EMA alignment on US equities. It is a comprehensive crypto strategy with multiple technical indicators.

## Strategy Logic

| Component | Parameters | Role |
|-----------|------------|------|
| EMA crossover | Fast 10 / Slow 50 (hourly) | Trend direction |
| RSI | 14-period Wilders | Overbought/oversold filter |
| Bollinger Bands | 20-period, 2σ | Mean reversion context |
| ATR volatility filter | 14-period, 60% threshold | Skip high-vol regimes |
| Trailing stop | 92% | Lock profits |
| Fixed stop | 88% | Capital protection |
| Take profit | 125% | Exit target |

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Multi-Layer-EMA"`

**QC Cloud:** Deployed as project 28433748.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Assets | BTCUSD, ETHUSD, LTCUSD |
| Resolution | Hourly |
| Max positions | 3 |
| Stop loss | Trailing 92%, Fixed 88% |
| Take profit | 125% |

## Files

- main.py - Strategy (OptimizedCryptoAlgorithm class)

# Crypto-MultiCanal

**Asset class:** Crypto (BTC)
**Cloud project ID:** 30750734

## Description

Multi-channel ZigZag strategy on Bitcoin. Uses 3 nested ZigZag channels (short/medium/long) to identify trend structure at multiple scale.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Crypto-MultiCanal"`

**QC Cloud:** Deployed as project 30750734.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | Multi-channel ZigZag |
| Universe | BTCUSD |
| Channels | 3 (nested) |

## Files

- main.py - Strategy (v17, multi-channel ZigZag)

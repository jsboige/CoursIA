# BTC-MACD-ADX

> **Archived 2026-05-29** — Misleading name: code is a simple EMA(12/26) crossover + ATR volatility filter (Main.cs L64: "Simplifie depuis MACD+ADX adaptatif"). The MACD and ADX indicators are NOT used. Different from [CSharp-BTC-EMA-Cross](../../CSharp-BTC-EMA-Cross) (which uses EMA 18/23 with cross margins, charts, and $600K capital). Research.ipynb is an unrelated QC template (Uncorrelated Assets).

**Asset class:** Crypto (BTC)
**Cloud project ID:** None (local only)

## Description

Bitcoin MACD + ADX trend-following strategy. Enters when MACD crosses above signal AND ADX > 25 (strong trend).

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/BTC-MACD-ADX"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | MACD + ADX trend filter |
| Universe | BTCUSD |
| Rebalance | Daily |

## Files

- main.py - Strategy

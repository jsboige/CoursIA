# Dataset Download Scripts

Collection of scripts for downloading and managing historical market data for QuantConnect strategies and educational notebooks.

## Scripts

| Script | Source | Output |
|--------|--------|--------|
| `download_yfinance.py` | yfinance (Yahoo Finance) | CSV per symbol |
| `download_binance_archive.py` | Binance public archives | CSV per period |
| `download_kaggle.py` | Kaggle datasets | Extracted files |
| `download_qc_data.py` | QuantConnect (lean-cli / Object Store) | QC data files |
| `manage_crypto_archive.py` | yfinance + CoinGecko fallback | Consolidated CSV per asset |

## Quick Start

### Stock/ETF data (yfinance)

```bash
# Single symbol
python scripts/datasets/download_yfinance.py --symbols SPY --start 2020-01-01 --end 2024-01-01

# Multiple symbols
python scripts/datasets/download_yfinance.py --symbols SPY,AAPL,TLT,GLD --start 2018-01-01

# Crypto via yfinance
python scripts/datasets/download_yfinance.py --symbols BTC-USD,ETH-USD --start 2019-01-01
```

Output: `MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/{SYMBOL}_{start}_{end}.csv`

Cache: Parquet files in `datasets/yfinance_cache/` (use `--no-cache` to bypass).

### Binance historical klines

```bash
# Daily BTC/USDT for 2023
python scripts/datasets/download_binance_archive.py --symbol BTCUSDT --start 2023-01-01 --end 2023-12-31

# Hourly ETH/USDT futures
python scripts/datasets/download_binance_archive.py --symbol ETHUSDT --market futures --interval 1h --start 2023-01-01
```

Output: `MyIA.AI.Notebooks/QuantConnect/datasets/binance/{SYMBOL}_{INTERVAL}_{DATE}.csv`

Intervals: `1m`, `5m`, `15m`, `30m`, `1h`, `2h`, `4h`, `6h`, `8h`, `12h`, `1d`, `3d`, `1w`, `1mo`

Markets: `spot` (default), `futures` (USDM)

### Kaggle datasets

```bash
# Download a dataset
python scripts/datasets/download_kaggle.py --dataset stefanoleone992/mutual-fund-etf-dataset

# Search datasets
python scripts/datasets/download_kaggle.py --list --search "crypto historical"
```

Output: `MyIA.AI.Notebooks/QuantConnect/datasets/kaggle/{dataset_slug}/`

Prerequisite: `pip install kaggle` with `~/.kaggle/kaggle.json` configured.

### QuantConnect data

```bash
# Equity daily data via lean-cli
python scripts/datasets/download_qc_data.py --symbol SPY --start 2020-01-01 --end 2023-12-31

# Crypto minute data
python scripts/datasets/download_qc_data.py --symbol BTCUSD --security-type crypto --resolution minute --start 2023-01-01

# From Object Store
python scripts/datasets/download_qc_data.py --mode object-store --key my-datasets/spy_daily.csv --output spy_daily.csv
```

Output: `MyIA.AI.Notebooks/QuantConnect/datasets/qc/`

Prerequisite: `pip install lean` + `lean login` for lean-cli mode.

### Crypto archive (multi-source)

```bash
# Build full BTC archive (2015-2024)
python scripts/datasets/manage_crypto_archive.py --symbol BTC --start 2015-01-01 --end 2024-12-31

# Build ETH archive
python scripts/datasets/manage_crypto_archive.py --symbol ETH --start 2017-01-01

# Update existing archive with new data
python scripts/datasets/manage_crypto_archive.py --symbol BTC --update

# List available archives
python scripts/datasets/manage_crypto_archive.py --list
```

Output: `MyIA.AI.Notebooks/QuantConnect/datasets/crypto_archive/{SYMBOL}_USDT_archive.csv`

Supported symbols: BTC, ETH, BNB, SOL, XRP, ADA, DOGE, DOT

Primary source: yfinance. Fallback: CoinGecko (via `pycoingecko`).

## Common Options

All scripts accept `--output-dir` to override the default output path.

| Default path | Script |
|--------------|--------|
| `datasets/yfinance/` | download_yfinance.py |
| `datasets/binance/` | download_binance_archive.py |
| `datasets/kaggle/` | download_kaggle.py |
| `datasets/qc/` | download_qc_data.py |
| `datasets/crypto_archive/` | manage_crypto_archive.py |

## Prerequisites

```bash
# Core (required by all)
pip install pandas

# Per-script
pip install yfinance          # download_yfinance.py, manage_crypto_archive.py
pip install requests          # download_binance_archive.py
pip install kaggle            # download_kaggle.py
pip install lean              # download_qc_data.py (lean-cli mode)
pip install pycoingecko       # manage_crypto_archive.py (CoinGecko fallback)
```

## Output Format

All scripts output CSV files with standard OHLCV columns where applicable:

| Script | Columns |
|--------|---------|
| yfinance | Date, Open, High, Low, Close, Volume |
| Binance | open_time, open, high, low, close, volume, close_time, quote_volume, trades, ... |
| Crypto archive | date, close, volume (+ market_cap from CoinGecko) |

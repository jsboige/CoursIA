# Crypto Panier - 10 Coins Daily OHLCV

Stage 3a anti-bias dataset for multi-asset ML training (Stage 3).

## Source

yfinance (Yahoo Finance), downloaded 2026-05-06.

## Coverage

| Symbol | Start | End | Rows | Note |
|--------|-------|-----|------|------|
| BTC-USD | 2018-01-01 | 2026-04-30 | 3042 | Full range |
| ETH-USD | 2018-01-01 | 2026-04-30 | 3042 | Full range |
| LTC-USD | 2018-01-01 | 2026-04-30 | 3042 | Full range |
| XRP-USD | 2018-01-01 | 2026-04-30 | 3042 | Full range |
| ADA-USD | 2018-01-01 | 2026-04-30 | 3042 | Full range |
| LINK-USD | 2018-01-01 | 2026-04-30 | 3042 | Full range |
| SOL-USD | 2020-04-10 | 2026-04-30 | 2212 | Listings 2020 |
| MATIC-USD | 2019-04-28 | 2025-03-24 | 2158 | Delisted/rebranded to POL |
| AVAX-USD | 2020-07-13 | 2026-04-30 | 2049 | Listings 2020 |
| DOT-USD | 2020-08-20 | 2026-04-30 | 2080 | Listings 2020 |

## Format

CSV, columns: `Date,Open,High,Low,Close,Volume`

- Date: YYYY-MM-DD (daily)
- Prices: float, USD
- Volume: int, daily traded volume

## Anti-bias design

5 coins with full 2018+ coverage (BTC, ETH, LTC, XRP, ADA, LINK) prevent the model from overfitting to a single asset's return distribution. 4 coins with shorter histories test generalization to newer assets. MATIC tests handling of delisted/rebranded assets.

## Regeneration

```bash
conda activate base
python -c "
import yfinance as yf, pandas as pd, os
COINS = ['BTC-USD','ETH-USD','LTC-USD','XRP-USD','ADA-USD',
         'DOT-USD','SOL-USD','AVAX-USD','MATIC-USD','LINK-USD']
for t in COINS:
    df = yf.download(t, start='2018-01-01', end='2026-05-01', auto_adjust=True, progress=False)
    if isinstance(df.columns, pd.MultiIndex): df.columns = df.columns.get_level_values(0)
    df = df[['Open','High','Low','Close','Volume']]
    df.index.name = 'Date'
    df.to_csv(f'{t}_2018-01-01_2026-05-01.csv')
"
```

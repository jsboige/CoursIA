# Panier Crypto - 10 Coins OHLCV Journalier

Dataset anti-biais de l'étape 3a pour l'entraînement ML multi-actifs (étape 3).

## Source

yfinance (Yahoo Finance), téléchargé le 2026-05-06.

## Couverture

| Symbole | Début | Fin | Lignes | Note |
|---------|-------|-----|--------|------|
| BTC-USD | 2018-01-01 | 2026-04-30 | 3042 | Plage complète |
| ETH-USD | 2018-01-01 | 2026-04-30 | 3042 | Plage complète |
| LTC-USD | 2018-01-01 | 2026-04-30 | 3042 | Plage complète |
| XRP-USD | 2018-01-01 | 2026-04-30 | 3042 | Plage complète |
| ADA-USD | 2018-01-01 | 2026-04-30 | 3042 | Plage complète |
| LINK-USD | 2018-01-01 | 2026-04-30 | 3042 | Plage complète |
| SOL-USD | 2020-04-10 | 2026-04-30 | 2212 | Cotation 2020 |
| MATIC-USD | 2019-04-28 | 2025-03-24 | 2158 | Delisted/rebrandé en POL |
| AVAX-USD | 2020-07-13 | 2026-04-30 | 2049 | Cotation 2020 |
| DOT-USD | 2020-08-20 | 2026-04-30 | 2080 | Cotation 2020 |

## Format

CSV, colonnes : `Date,Open,High,Low,Close,Volume`

- Date : AAAA-MM-JJ (journalier)
- Prix : float, USD
- Volume : int, volume échangé journalier

## Conception anti-biais

6 coins avec une couverture complète 2018+ (BTC, ETH, LTC, XRP, ADA, LINK) empêchent le modèle de surajuster la distribution de rendement d'un seul actif. 4 coins avec un historique plus court testent la généralisation à des actifs plus récents. MATIC teste la gestion des actifs delisted/rebrandés.

## Régénération

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

# Scripts de téléchargement de datasets

> Version anglaise originale préservée dans [README.en.md](README.en.md).

Collection de scripts pour télécharger et gérer les données de marché historiques utilisées par les stratégies QuantConnect et les notebooks pédagogiques.

## Scripts

| Script | Source | Sortie |
|--------|--------|--------|
| `download_yfinance.py` | yfinance (Yahoo Finance) | CSV par symbole |
| `download_binance_archive.py` | Archives publiques Binance | CSV par période |
| `download_kaggle.py` | Jeux de données Kaggle | Fichiers extraits |
| `download_qc_data.py` | QuantConnect (lean-cli / Object Store) | Fichiers de données QC |
| `manage_crypto_archive.py` | yfinance + fallback CoinGecko | CSV consolidé par actif |
| `stitch_crypto.py` | Bitstamp + Binance + yfinance | CSV continu horaire BTC/USD |
| `build_panier_anti_bias.py` | yfinance (26 symboles, 7 classes d'actifs) | CSV panier multi-actifs |
| `dezip_forex.py` | Archives zip FXCM/Oanda | CSV OHLCV forex bid/ask |

## Démarrage rapide

### Données actions/ETF (yfinance)

```bash
# Symbole unique
python scripts/datasets/download_yfinance.py --symbols SPY --start 2020-01-01 --end 2024-01-01

# Plusieurs symboles
python scripts/datasets/download_yfinance.py --symbols SPY,AAPL,TLT,GLD --start 2018-01-01

# Crypto via yfinance
python scripts/datasets/download_yfinance.py --symbols BTC-USD,ETH-USD --start 2019-01-01
```

Sortie : `MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/{SYMBOL}_{start}_{end}.csv`

Cache : fichiers Parquet dans `datasets/yfinance_cache/` (utiliser `--no-cache` pour contourner).

### Klines historiques Binance

```bash
# BTC/USDT journalier pour 2023
python scripts/datasets/download_binance_archive.py --symbol BTCUSDT --start 2023-01-01 --end 2023-12-31

# Futures ETH/USDT horaires
python scripts/datasets/download_binance_archive.py --symbol ETHUSDT --market futures --interval 1h --start 2023-01-01
```

Sortie : `MyIA.AI.Notebooks/QuantConnect/datasets/binance/{SYMBOL}_{INTERVAL}_{DATE}.csv`

Intervalles : `1m`, `5m`, `15m`, `30m`, `1h`, `2h`, `4h`, `6h`, `8h`, `12h`, `1d`, `3d`, `1w`, `1mo`

Marchés : `spot` (par défaut), `futures` (USDM)

### Jeux de données Kaggle

```bash
# Télécharger un dataset
python scripts/datasets/download_kaggle.py --dataset stefanoleone992/mutual-fund-etf-dataset

# Rechercher des datasets
python scripts/datasets/download_kaggle.py --list --search "crypto historical"
```

Sortie : `MyIA.AI.Notebooks/QuantConnect/datasets/kaggle/{dataset_slug}/`

Pré-requis : `pip install kaggle` avec `~/.kaggle/kaggle.json` configuré.

### Données QuantConnect

```bash
# Données actions journalières via lean-cli
python scripts/datasets/download_qc_data.py --symbol SPY --start 2020-01-01 --end 2023-12-31

# Données crypto à la minute
python scripts/datasets/download_qc_data.py --symbol BTCUSD --security-type crypto --resolution minute --start 2023-01-01

# Depuis l'Object Store
python scripts/datasets/download_qc_data.py --mode object-store --key my-datasets/spy_daily.csv --output spy_daily.csv
```

Sortie : `MyIA.AI.Notebooks/QuantConnect/datasets/qc/`

Pré-requis : `pip install lean` + `lean login` pour le mode lean-cli.

### Archive crypto (multi-sources)

```bash
# Construire l'archive complète BTC (2015-2024)
python scripts/datasets/manage_crypto_archive.py --symbol BTC --start 2015-01-01 --end 2024-12-31

# Construire l'archive ETH
python scripts/datasets/manage_crypto_archive.py --symbol ETH --start 2017-01-01

# Mettre à jour une archive existante avec de nouvelles données
python scripts/datasets/manage_crypto_archive.py --symbol BTC --update

# Lister les archives disponibles
python scripts/datasets/manage_crypto_archive.py --list
```

Sortie : `MyIA.AI.Notebooks/QuantConnect/datasets/crypto_archive/{SYMBOL}_USDT_archive.csv`

Symboles supportés : BTC, ETH, BNB, SOL, XRP, ADA, DOGE, DOT

Source principale : yfinance. Fallback : CoinGecko (via `pycoingecko`).

### Stitching crypto (BTC/USD continu)

```bash
# Assembler Bitstamp + Binance + yfinance en série horaire continue
python scripts/datasets/stitch_crypto.py

# Racine de données personnalisée pour archives personnelles
python scripts/datasets/stitch_crypto.py --data-root /path/to/data --output-dir datasets/crypto/

# Sauter le téléchargement yfinance (mode hors-ligne)
python scripts/datasets/stitch_crypto.py --skip-download
```

Sortie : `datasets/crypto/BTC_USD_1h_stitched.csv` (~101K lignes, 2013-2024)

Sources (ordre de priorité) : Bitstamp 1h (primaire 2018-2024), Binance BTC/USDT (extension avant 2018), yfinance (comblement des trous jusqu'à aujourd'hui).

Note : les données 2011-2012 sont exclues par défaut (`--start-date 2013-01-01`). 2011 n'avait que 307/8760 heures avec des trous massifs. 2012 n'avait que 62,6% de couverture (5501/8784h) avec des trous récurrents de 10-22h.

### Panier anti-biais (multi-actifs)

```bash
# Télécharger et valider les 26 symboles
python scripts/datasets/build_panier_anti_bias.py

# Plage temporelle personnalisée
python scripts/datasets/build_panier_anti_bias.py --start 2018-01-01 --end 2026-01-01

# Valider uniquement les fichiers existants (pas de téléchargement)
python scripts/datasets/build_panier_anti_bias.py --validate-only

# Utiliser les fichiers en cache (pas de nouveau téléchargement)
python scripts/datasets/build_panier_anti_bias.py --skip-download
```

Sortie : `datasets/panier/` avec CSV par symbole + `panier_close_all.csv` + `panier_report.json`

**Politique anti-biais** : les symboles INTERDITS (AAPL, MSFT, GOOG, AMZN, NVDA, TSLA, META) sont exclus. Le panier couvre 7 classes d'actifs : actions US broad/sectorielles, volatilité, obligations, matières premières, international, crypto.

### Extraction de données forex

```bash
# Lister le contenu de l'archive
python scripts/datasets/dezip_forex.py --list

# Extraire les données journalières
python scripts/datasets/dezip_forex.py --extract daily

# Extraire les données horaires
python scripts/datasets/dezip_forex.py --extract hourly

# Tout extraire
python scripts/datasets/dezip_forex.py --extract all
```

Sortie : `datasets/forex/` avec CSV par paire et par résolution (OHLCV mid-price + spread).

Source : archives zip imbriquées FXCM/Oanda avec données OHLCV bid/ask.

## Options communes

Tous les scripts acceptent `--output-dir` pour surcharger le chemin de sortie par défaut.

| Chemin par défaut | Script |
|--------------|--------|
| `datasets/yfinance/` | download_yfinance.py |
| `datasets/binance/` | download_binance_archive.py |
| `datasets/kaggle/` | download_kaggle.py |
| `datasets/qc/` | download_qc_data.py |
| `datasets/crypto_archive/` | manage_crypto_archive.py |
| `datasets/crypto/` | stitch_crypto.py |
| `datasets/panier/` | build_panier_anti_bias.py |
| `datasets/forex/` | dezip_forex.py |

## Pré-requis

```bash
# Cœur (requis par tous)
pip install pandas

# Par script
pip install yfinance          # download_yfinance.py, manage_crypto_archive.py
pip install requests          # download_binance_archive.py
pip install kaggle            # download_kaggle.py
pip install lean              # download_qc_data.py (mode lean-cli)
pip install pycoingecko       # manage_crypto_archive.py (fallback CoinGecko)
```

## Format de sortie

Tous les scripts produisent des fichiers CSV avec les colonnes OHLCV standard lorsque applicable :

| Script | Colonnes |
|--------|---------|
| yfinance | Date, Open, High, Low, Close, Volume |
| Binance | open_time, open, high, low, close, volume, close_time, quote_volume, trades, ... |
| Archive crypto | date, close, volume (+ market_cap depuis CoinGecko) |
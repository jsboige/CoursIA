# Panier Anti-Biais - 26 Symboles OHLCV Journalier

Dataset diversifié multi-actifs pour l'entraînement ML (Epic #1409 / #4921),
utilisé par les notebooks de recherche du pipeline ML-Training-Pipeline
(L1 tsmom, L2 dual momentum, ...).

## Politique anti-biais

Symboles **interdits** dans le training set : AAPL, MSFT, GOOG, AMZN, NVDA, TSLA, META.
Objectif : éviter le sur-apprentissage aux FAANG/Mag7 et forcer la
diversification sectorielle / asset-class.

## Couverture (7 classes d'actifs, 26 symboles)

| Classe | Symboles | Count |
|--------|----------|-------|
| us_equity_broad | SPY, RSP, IWM | 3 |
| us_equity_sectors | XLF, XLK, XLV, XLY, XLP, XLI, XLU, XLB, XLRE, XLC | 10 |
| volatility | ^VIX | 1 |
| us_bonds | TLT, IEF, SHY | 3 |
| commodities | GLD, USO, DBA | 3 |
| international | EFA, EEM | 2 |
| crypto | BTC-USD, ETH-USD, LTC-USD, XRP-USD | 4 |

Plage : 2015-01-01 -> aujourd'hui (CSV filename encode les bornes effectives).
Crypto : BTC/LTC cote depuis 2015, ETH/XRP depuis fin 2017.
XLRE : cote depuis octobre 2015, XLC depuis juin 2018.

## Format

CSV, colonnes : `Date,Open,High,Low,Close,Volume`

- Date : AAAA-MM-JJ (journalier)
- Prix : float, USD
- Volume : int, volume échangé journalier

Fichiers additionnels :
- `panier_close_all.csv` : matrice panel (rows=dates, cols=symboles), closes only, NaN pour dates de cotation manquantes.
- `panier_report.json` : rapport de validation (rows par symbole, nan_close, group).

## Construction / rebuild

```bash
# Build complet (télécharge les 26 symboles via yfinance, ~10s en cache warm)
python scripts/datasets/build_panier_anti_bias.py --start 2015-01-01

# Re-build rapide si déjà en cache
python scripts/datasets/build_panier_anti_bias.py --start 2015-01-01 --skip-download
```

Cache yfinance : `scripts/datasets/yfinance_cache/` (Parquet, MD5-cache-key).
Les CSVs sont gitignored (cf `.gitignore` ligne 94 `datasets/`) - ce README
est forcé-tracké pour la reproductibilité fresh-clone.

## Utilisation dans les notebooks

Le helper `scripts/datasets/panier_loader.py` (dans ML-Training-Pipeline/scripts/)
charge ce dataset avec `auto_fetch=False` (pas d'appel réseau) :

```python
from panier_loader import load_panier_closes, PANIER_GROUPS

closes = load_panier_closes(auto_fetch=False).dropna(how="all")
```

Voir `research_l1_tsmom.ipynb` / `research_l2_dual_momentum.ipynb` pour les
exemples d'usage dans le pipeline ML-Training-Pipeline.
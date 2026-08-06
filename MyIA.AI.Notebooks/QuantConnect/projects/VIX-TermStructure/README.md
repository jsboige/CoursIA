# VIX-TermStructure

**Classe d'actifs :** Volatilité (SVXY)
**Cloud project ID :** None (local only)
**Statut :** ARCHIVED (plafond Sharpe +0.05)

## Description

Stratégie de term structure VIX utilisant SVXY (ETF short-volatility).
Signaux basés sur le spread entre le VIX spot et le VIX3M (futures VIX à 3 mois).
Prend position long SVXY quand la term structure est en contango (VIX < VIX3M), à plat en backwardation.

**Archivée car :** Plafond structurel à Sharpe +0.05. Les stratégies short-vol souffrent de
paiements asymétriques (petits gains, pertes catastrophiques rares). L'événement Volmageddon de 2018
démontre le risque structurel. Voir ARCHIVE.md pour l'analyse complète du plafond.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/VIX-TermStructure"`
```bash
lean backtest --project .
```

**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

### Données VIX (quantbook)

Le quantbook charge les séries VIX / VIX3M depuis des CSV locaux (`vix_daily.csv`,
`vix3m_daily.csv`). `qb.add_data(CBOE, ...)` nécessite l'infra alternative-data de
QC Cloud (vide en recherche Docker locale) ; VIX/VIX3M sont les **indices publics
CBOE** (volatilité implicite 30 / 93 jours), disponibles gratuitement via yfinance
(`^VIX` / `^VIX3M`). Les CSV sont **gitignorés** (`*.csv` sous `projects/`) — pour
les régénérer de façon reproductible (1 commande) :

```bash
python scripts/quantconnect/provision_vix_csv.py --out-folder lean-workspace/data
```

Écrit les deux CSV dans le dossier de données LEAN (le point de montage Docker
`/Lean/Data/`), où le quantbook les trouve via son `_find()`.

## Métriques de backtest (2015-2026)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | +0.05 |
| Stratégie | Long SVXY en contango |
| Signal | Spread VIX vs VIX3M |
| Risque | Risque de queue Volmageddon |

## Fichiers

- main.py - Stratégie (v4.1, signal contango term structure VIX)
- research.ipynb - Analyse du spread VIX et test de régimes

## Références

- Simon & Campasano (2014), "The VIX Fix"
- ARCHIVE.md - Historique complet des itérations et analyse du plafond structurel

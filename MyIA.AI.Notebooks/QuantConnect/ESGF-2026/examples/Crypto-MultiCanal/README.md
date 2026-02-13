# Detecteur Hierarchique Multi-Canaux (ID: 22298373)

Strategie de detection de canaux de prix a plusieurs echelles temporelles pour BTCUSDT.
C'est le projet le plus avance du portfolio, issu d'un travail iteratif sur plusieurs mois.

## Architecture

```
Prix BTCUSDT (Hourly)
    |
    v
ZigZag (seuil 5%)
    |
    v
Pivots (Hauts -1 / Bas +1)
    |
    +---> Macro (500j lookback) --> Resistance + Support
    |         |
    |         v (filtre temporel: 2e pivot macro le plus recent)
    |
    +---> Meso (150j lookback) --> Resistance + Support
    |         |
    |         v (filtre temporel: 2e pivot meso le plus recent)
    |
    +---> Micro (50j lookback) --> Resistance + Support
    |
    v
Signaux: Breakout (cassure) ou Bounce (rebond)
    |
    v
Gestion SL/TP avec OCO (One-Cancels-Other)
```

## Algorithme de detection des canaux

Pour chaque echelle (Macro/Meso/Micro), les lignes de resistance et support sont trouvees par :

1. **Enumeration** de toutes les paires de pivots de meme type (hauts pour resistance, bas pour support)
2. **Validation stricte** : tous les autres pivots doivent etre du bon cote de la ligne
3. **Scoring WSSE** (Weighted Sum of Squared Errors) : les pivots recents ont plus de poids
4. **Selection** : la ligne avec le WSSE le plus faible est retenue

Les canaux sont hierarchiques : Meso utilise les pivots apres le 2e pivot Macro le plus recent, et Micro apres le 2e pivot Meso le plus recent.

## Parametres GA (optimises par algorithme genetique)

```python
strategy_params = {
    'trade_level': 'meso',              # Niveau de trading
    'signal_type': 'breakout',          # Type de signal
    'trend_filter_level': 'none',       # Filtre de tendance
    'risk_per_trade_pct': 0.0199,       # Risque par trade (~2%)
    'min_channel_width_pct': 0.0062,    # Largeur minimum du canal
    'breakout_sl_type': 'pct_level',    # SL en % du niveau casse
    'breakout_sl_value': 0.0120,        # SL = 1.2% sous le niveau
    'breakout_tp_type': 'rr_ratio',     # TP en ratio Risk/Reward
    'breakout_tp_value': 2.9670,        # TP = ~3x le risque
}
```

## Parametres des canaux

```python
channel_params = {
    "wp_macro_res": 2.0,   # Poids temporel WSSE (macro resistance)
    "rpf_macro_res": 1.0,  # Fraction de pivots recents pour WSSE
    "wp_meso_res": 2.0,
    "rpf_meso_res": 1.0,
    "wp_micro_res": 2.0,
    "rpf_micro_res": 1.0,
    "wp_micro_sup": 4.0,   # Micro support: poids plus fort sur les recents
    "rpf_micro_sup": 0.30, # Micro support: seulement 30% des pivots les plus recents
}
```

## Fichiers

| Fichier | Taille | Description |
|---------|--------|-------------|
| `main.py` | ~930 lignes | Algorithme complet : helpers, ZigZag, canaux, entrees/sorties, OCO |
| `fix_ipynb_quotes.py` | petit | Utilitaire de nettoyage pour le notebook research |
| `research.ipynb` | 210K | Notebook de recherche et visualisation (cloud QC) |
| `research_archive.ipynb` | archive | Version archivee du notebook research |

## Concepts pedagogiques

- **Detection de pivots** : ZigZag avec seuil de retracement configurable
- **Canaux de prix** : Regression lineaire stricte (pas de violation)
- **Multi-echelles** : Hierarchie Macro > Meso > Micro avec filtrage temporel
- **Gestion du risque** : Position sizing base sur le risque par trade
- **OCO Orders** : Stop Loss + Take Profit avec annulation croisee
- **Optimisation parametrique** : Parametres trouves par algorithme genetique

## Versions precedentes

- **C# v1** : `Exemple-CSharp-BTC-MACD-ADX-Daily-1` (ID 19898232) - base originale MACD+ADX
- **C# v2** : `BTC-MultiCanal-ZigZag-Hour-1` (ID 22275116) - seuils adaptatifs par percentiles
- **C# v2bis** : `BTC-MACD-ADX-Hour-1` (ID 20423659) - iteration horaire intermediaire
- **Python (actuel)** : Version la plus avancee avec GA et multi-canaux complets

## Configuration Backtest

- **Dates** : 2020-08-09 au 2025-04-01
- **Capital** : 10,000 USDT
- **Broker** : Binance Cash
- **Resolution** : Hourly
- **Recalcul** : Daily (00:05 UTC)
- **Warmup** : 510 jours (lookback macro + marge)

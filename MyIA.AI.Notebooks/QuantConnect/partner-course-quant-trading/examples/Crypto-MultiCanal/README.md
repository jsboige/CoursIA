# Détecteur Hiérarchique Multi-Canaux (ID: 22298373)

Stratégie de detection de canaux de prix a plusieurs échelles temporelles pour BTCUSDT.
C'est le projet le plus avancé du portfolio, issu d'un travail itératif sur plusieurs mois.

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

Pour chaque échelle (Macro/Meso/Micro), les lignes de résistance et support sont trouvées par :

1. **Énumération** de toutes les paires de pivots de même type (hauts pour résistance, bas pour support)
2. **Validation stricte** : tous les autres pivots doivent être du bon côté de la ligne
3. **Scoring WSSE** (Weighted Sum of Squared Errors) : les pivots récents ont plus de poids
4. **Sélection** : la ligne avec le WSSE le plus faible est retenue

Les canaux sont hiérarchiques : Meso utilise les pivots après le 2e pivot Macro le plus récent, et Micro après le 2e pivot Meso le plus récent.

## Paramètres GA (optimisés par algorithme génétique)

```python
strategy_params = {
    'trade_level': 'meso',              # Niveau de trading
    'signal_type': 'both',              # Type de signal (MODIFIE: breakout + bounce)
    'trend_filter_level': 'macro',      # Filtre de tendance (MODIFIE: active sur macro)
    'risk_per_trade_pct': 0.0199,       # Risque par trade (~2%)
    'min_channel_width_pct': 0.0062,    # Largeur minimum du canal
    'bounce_sl_type': 'pct_entry',      # SL bounce en % de l'entree
    'bounce_sl_value': 0.0105,          # SL bounce = 1.05%
    'bounce_tp_value': 2.1194,          # TP bounce = ~2.1x le risque
    'bounce_entry_offset': 0.0015,      # Offset d'entree bounce = 0.15%
    'breakout_sl_type': 'pct_level',    # SL en % du niveau casse
    'breakout_sl_value': 0.0120,        # SL = 1.2% sous le niveau
    'breakout_tp_type': 'rr_ratio',     # TP en ratio Risk/Reward
    'breakout_tp_value': 2.9670,        # TP = ~3x le risque
}
```

## Paramètres des canaux

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
| `main.py` | ~930 lignes | Algorithme complet : helpers, ZigZag, canaux, entrées/sorties, OCO |
| `fix_ipynb_quotes.py` | petit | Utilitaire de nettoyage pour le notebook research |
| `research.ipynb` | 210K | Notebook de recherche et visualisation (cloud QC) |
| `research_archive.ipynb` | archive | Version archivée du notebook research |

## Concepts pédagogiques

- **Détection de pivots** : ZigZag avec seuil de retracement configurable
- **Canaux de prix** : Régression linéaire stricte (pas de violation)
- **Multi-échelles** : Hiérarchie Macro > Meso > Micro avec filtrage temporel
- **Gestion du risque** : Position sizing basé sur le risque par trade
- **OCO Orders** : Stop Loss + Take Profit avec annulation croisée
- **Optimisation paramétrique** : Paramètres trouvés par algorithme génétique

## Versions précédentes

- **C# v1** : `Exemple-CSharp-BTC-MACD-ADX-Daily-1` (ID 19898232) - base originale MACD+ADX
- **C# v2** : `BTC-MultiCanal-ZigZag-Hour-1` (ID 22275116) - seuils adaptatifs par percentiles
- **C# v2bis** : `BTC-MACD-ADX-Hour-1` (ID 20423659) - itération horaire intermédiaire
- **Python (actuel)** : Version la plus avancée avec GA et multi-canaux complets

## Configuration Backtest

- **Dates** : 2020-08-09 au 2025-04-01
- **Capital** : 10,000 USDT
- **Broker** : Binance Cash
- **Resolution** : Hourly
- **Recalcul** : Daily (00:05 UTC)
- **Warmup** : 510 jours (lookback macro + marge)

## Changelog

### 2026-02-15 - Améliorations prioritaires

**Modifications appliquées dans `main.py`:**

1. **Default TP robuste** (lignes 223-230)
   - Ajout d'un Take Profit par défaut = 2x la distance du stop-loss
   - Évite les trades sans TP si le calcul RR échoue
   - Préserve la directionnalité (long/short)

2. **Activation du trend filter** (ligne 25)
   - `trend_filter_level`: 'none' → 'macro'
   - Filtre les entrées contre-tendance sur l'échelle macro
   - Améliore la qualité des signaux

3. **Activation des signaux bounce** (ligne 25)
   - `signal_type`: 'breakout' → 'both'
   - Active les signaux de rebond en plus des cassures
   - Augmente les opportunités de trading

**Statut compilation:** BuildSuccess (warnings linter non-bloquants)

**Prochaines étapes:**
- Lancer un backtest via l'interface web QC
- Analyser les métriques (Sharpe, Drawdown, Win Rate)
- Comparer avec les backtests précédents

# Options Income Strategies

Stratégies de génération de revenus via la vente d'options.

## Stratégie de `main.py` : Covered Call v7.0

`main.py` implémente une seule stratégie, un covered call sur SPY (`CoveredCallStrategy`).

| Paramètre | Valeur dans `main.py` |
|-----------|--------|
| **Sous-jacent** | SPY, 200 actions (2 contrats × 100) |
| **Option** | Vente de 2 calls OTM, delta cible ~0.20, échéance 20 à 45 jours (cible 30 j en repli) |
| **Filtre d'entrée** | Pas de vente si le VIX (CBOE) sort de [15, 35] |
| **Prise de profit** | Rachat du call quand il a perdu 50 % de sa prime |
| **Fermeture défensive** | Rachat du call si SPY baisse de plus de 3 % sur la séance |
| **Roll** | Rachat à 10 jours de l'échéance, ou dès que le strike passe sous 97 % du cours |
| **Période du backtest** | 2015-01-01 → 2024-12-31 |

Les variantes `main_v71_ivrank.py` (filtre IV-rank par sous-jacent à la place du filtre VIX global) et `main_v72_strikeavail.py` (second facteur, disponibilité des strikes) gardent les mêmes règles pour rester comparables à v7.0. Leur docstring porte le verdict mesuré : NO BEATS.

## Résultats de backtest (Covered Call, 2015-2024)

> Les métriques quantitatives (Total Return, Premium, Max Drawdown, Sharpe) sont
> machine-dépendantes : elles dérivent avec les données, la période et l'environnement
> d'exécution. Elles ne sont pas attestées par un backtest figé ici. Les obtenir via
> `lean backtest` (moteur Lean local) ou en poussant le projet sur QC Cloud.

## Fichiers

```
OptionsIncome/
├── main.py              # Covered Call v7.0 (filtre VIX)
├── main_v71_ivrank.py     # Variante v71 (filtre IV rank)
├── main_v72_strikeavail.py # Variante v72 (disponibilité des strikes)
├── research.ipynb       # Analyse options, Greeks, backtest
├── quantbook.ipynb      # QuantBook de recherche Covered Call (données natives QC)
└── README.md            # Ce fichier
```

## Configuration

```python
# Covered Call (main.py, initialize)
self.target_delta = 0.20        # delta cible du call vendu
self.days_to_roll = 10          # jours avant échéance pour le roll
self.num_contracts = 2          # contrats vendus (200 actions couvertes)
self.vix_min = 15               # pas de vente sous ce VIX
self.vix_max = 35               # pas de vente au-dessus
self.profit_target = 0.50       # rachat à 50 % de la prime
self.defensive_drop = 0.03      # rachat si SPY perd plus de 3 % sur la séance
```

## Points Clés

- **Profit max**: Strike - Prix d'achat + Premium
- **Perte max**: Prix d'achat - Premium (comme détenir l'action)
- **Idéal**: Marchés légèrement haussiers à neutres

## Risques

- **Baisse du sous-jacent**: la prime n'amortit qu'une petite part de la perte, et le gain à la hausse est plafonné au strike
- **Assignment**: Options américaines peuvent être exercées tôt
- **Liquidité**: Vérifier open interest > 100

## Améliorations Possibles

- Delta dynamique basé sur VIX
- Roll "up and out" si très bullish
- Gestion de la gamma risk proche expiration
- Stop-loss basé sur % du premium
- Iron Condor sur SPY (short put spread + short call spread) : présenté dans une version antérieure de ce README, il n'est implémenté dans aucun fichier du projet

## Références

- Notebook: QC-Py-06-Options-Trading.ipynb
- CBOE: Options Strategy Guide

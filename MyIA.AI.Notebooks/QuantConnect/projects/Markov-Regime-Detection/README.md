# Markov-Regime-Detection

**Classe d'actifs :** Actions/ETF américains (SPY, TLT, GLD)
**ID projet Cloud :** `36387308`

## Description

Détection de régime markovien avec `MarkovRegression` de statsmodels. Identifie 2 régimes (haussier/baissier) sur les rendements de SPY, arbitre mensuellement entre SPY (régime calme) et TLT (régime agité), avec une couche GLD constante de 10 %.

**Consolidé depuis ML-HMM-Regime** (copie quasi-identique avec même nom de classe, même `k_regimes=2`, même logique d'allocation).

## Overlay Fear & Greed (v1.2, #15534)

Le projet consolide l'article de recherche QuantConnect [#19465](https://www.quantconnect.com/research/19465/filtering-trades-with-the-fear-and-greed-index/) sous forme d'un **overlay optionnel**, activé par le paramètre `use_feargreed` (défaut `0` = comportement v1.1 strictement inchangé).

**Source primaire** : Huang, Jiang, Tu & Zhou (2015), « Investor Sentiment Aligned: A Powerful Predictor of Stock Returns », *Review of Financial Studies* 28(3), 791-837 — l'indice de sentiment aligné comme prédicteur puissant des rendements. L'article QuantConnect reste le point d'entrée opérationnel, cette référence est la source académique primaire.

**Mécanisme** : le même outil que le régime principal (`MarkovRegression`, `k_regimes=2`) est ajusté sur l'historique glissant de l'indice Fear & Greed, et l'exposition SPY est **réduite de moitié** quand le régime SPY demande du risque mais que le régime de l'indice est dans son état « greedy » (le reste demeure en cash — jamais en TLT, qui mélangerait deux signaux de régime). Le régime « greedy » est identifié par sa **moyenne ajustée** plus élevée, jamais par un numéro de régime codé en dur, pour qu'un renumérotage entre ajustements ne puisse pas inverser silencieusement le filtre.

**Dataset** : `FearGreedIndex`, exposé par le wildcard `AlgorithmImports` (aucun import explicite), ticker `"FG"`. Sonde de disponibilité mesurée sur QC Cloud le 2026-09-11 : ≥ 2500 lignes quotidiennes livrées jusqu'à déc. 2025, couverture depuis juillet 2014, non gated.

**Seeds** : le balayage de seeds de l'article (30-50) n'a pas d'objet ici — l'article tirait des trades aléatoires, alors que cette stratégie est un arbitrage mensuel déterministe dont l'ajustement `MarkovRegression` ne dépend d'aucune graine. La robustesse est donc testée par **sous-périodes de marché** à la place.

## Comment lancer

**QC Cloud :** projet `36387308` (public). Paramètres : `use_feargreed` (0/1), `start_year`/`end_year`, `lookback_years` (défaut 3).
**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Markov-Regime-Detection"`

## Métriques de backtest

Mesurées le 2026-09-11 sur QC Cloud, frais Interactive Brokers conservés dans les deux bras (contrairement à l'article, qui les supprimait par `ConstantFeeModel(0)`), réajustement mensuel. Le bras A est la baseline (`use_feargreed=0`), le bras B la variante (`use_feargreed=1`) ; chaque fenêtre est un run indépendant (pas une tranche du run complet), le réchauffement de 3 ans et l'état de régime n'étant pas reportés d'une fenêtre à l'autre.

| Fenêtre | Bras | Sharpe | CAGR | MaxDD | Profit net | Profit net ($) | PSR | Ordres |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| 2015-2026 | A — baseline | 0.290 | 7.182 % | 23.700 % | 114.572 % | 74 574.09 | 0.197 % | 103 |
| 2015-2026 | B — variante | 0.019 | 3.318 % | 26.300 % | 43.243 % | 23 093.34 | 0.004 % | 105 |
| IS 2015-2020 | A — baseline | 0.229 | 4.735 % | 16.700 % | 26.038 % | 14 496.06 | 1.859 % | 44 |
| IS 2015-2020 | B — variante | 0.051 | 2.653 % | 14.500 % | 13.996 % | 7 532.51 | 0.526 % | 45 |
| OOS 2021-2026 | A — baseline | 0.297 | 8.991 % | 23.700 % | 53.825 % | 26 626.13 | 2.596 % | 41 |
| OOS 2021-2026 | B — variante | −0.123 | 3.278 % | 22.500 % | 17.510 % | 2 344.36 | 0.121 % | 42 |

**Verdict : NO BEATS sur les trois fenêtres.** L'overlay dégrade le Sharpe (jusqu'à le rendre négatif en OOS), le CAGR et le profit net partout. La seule métrique où B fait mieux est le MaxDD en IS (14.500 % contre 16.700 %), conséquence mécanique d'une exposition réduite de moitié et non d'un meilleur signal. Le nombre d'ordres est quasi identique dans chaque fenêtre (103/105, 44/45, 41/42), ce qui est le comportement attendu d'un overlay qui ne modifie que le **poids** d'exposition et jamais la fréquence de décision — le turnover n'étant pas exposé par l'outil de lecture (qc-mcp-lite mappe six statistiques), le nombre d'ordres en est le proxy déclaré.

## Fichiers

- `main.py` - Stratégie (v1.2, régime markovien + overlay Fear & Greed optionnel)
- `README.en.md` - Version anglaise

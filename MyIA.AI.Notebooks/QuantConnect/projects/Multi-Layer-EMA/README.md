# Multi-Layer-EMA — Stratégie crypto multi-indicateurs (EMA + RSI + Bollinger + ATR)

**Classe d'actifs :** Crypto (BTCUSDT, ETHUSDT, LTCUSDT sur Binance)
**Résolution :** Quotidienne
**Cloud project ID :** 28433748
**Période backtestée :** 2018-01-01 → 2024-12-31

## Description

Stratégie crypto multi-indicateurs combinant tendance EMA, RSI, bandes de Bollinger et filtre de volatilité ATR. L'entrée exige un croisement EMA (rapide/lente) **confirmé** par les conditions RSI et Bollinger, avec un **gate de volatilité ATR** : aucune nouvelle entrée quand la volatilité annualisée du BTC (ATR 14 rapporté au prix) dépasse 60 %. Les stops, la prise de bénéfice et la sortie sur croisement restent évalués chaque jour (correction #23460, voir plus bas).

**Note** : malgré le nom du répertoire, cette stratégie **n'est pas** un simple alignement multi-couches EMA sur actions US. C'est une stratégie crypto complète à plusieurs indicateurs techniques — le nom reflète l'historique du répertoire, pas la stratégie déployée.

**Version anglaise préservée** : [README.en.md](README.en.md).

## Logique de la stratégie

| Composant | Paramètres | Rôle |
|-----------|------------|------|
| Croisement EMA | Rapide 10 / Lente 50 (quotidien) | Direction de tendance |
| RSI | 14 périodes (Wilder) | Filtre surachat/survente |
| Bandes de Bollinger | 20 périodes, 2σ | Contexte de mean-reversion |
| Filtre volatilité ATR | 14 périodes, seuil 60 % (annualisé quotidien) | Bloquer les nouvelles entrées en régime haute volatilité |
| Trailing stop | 92 % | Sécuriser les gains |
| Stop fixe | 88 % | Protection du capital |
| Take profit | 125 % | Objectif de sortie |

## Backtest publié (QC Cloud, modèle de courtage Binance)

Vérifié sur QC Cloud (project 28433748, 2018-01-01 → 2024-12-31). Backtest de confirmation frais 2026-08-06 : les métriques documentées se reproduisent. **Elles portent sur le filtre d'origine (`gate=legacy`)**, qui suspendait les stops : voir la correction ci-dessous.

| Métrique | Valeur | (backtest frais 2026-08-06) |
|----------|--------|------------------------------|
| Sharpe ratio | 0.798 | **0.799** (confirme) |
| CAGR | 24.99 % | **24.99 %** (confirme) |
| Drawdown max | 57.1 % | **57.1 %** (confirme) |
| Ordres exécutés | 196 | **196** (confirme) |
| PSR | — | **19.26 %** |
| Rendement total net | — | 377.4 % |

| Configuration | Valeur |
|---------------|-------|
| Actifs | BTCUSDT, ETHUSDT, LTCUSDT (Binance) |
| Résolution | Quotidienne |
| Positions max | 3 |
| Stop loss | Trailing 92 %, Fixe 88 % |
| Take profit | 125 % |

## Correction #23460 — le filtre de volatilité suspendait les stops

**Le défaut.** Dans la version d'origine, le filtre de volatilité faisait `return` en tête de `OnData`, avant la boucle qui évalue les stops, la prise de bénéfice et la sortie sur croisement. Tant que le filtre était actif, une ligne détenue n'était plus surveillée. Le README disait l'inverse (« elle sort pendant les crashs via le gate ATR »).

**Le correctif.** Le paramètre `gate` vaut `entries` par défaut : le filtre ne bloque plus que les nouvelles entrées, et les sorties sont évaluées chaque jour. `gate=legacy` garde le code d'origine à l'identique. La décision (EMA 10/50, RSI, Bollinger, seuils, stops, allocation 0,7/3) ne change pas, et aucun paramètre n'a été re-réglé. Autres paramètres : `mode` (`strategy`, `btc`, `ew70`), `start_date`, `end_date`. Trace `shadow` (#18923) et statistiques d'exécution `gate_days`, `gate_days_invested`, `suspended_breaches`, `stop_exits`, `gate_stop_exits`, `max_stop_overshoot`.

**Mesure** (protocole écrit dans #23460 avant les runs ; QC Cloud, 2026-10-30, huit backtests lus à `completed: true`, même code vérifié par empreinte). `btc` : BTC acheté le premier jour et détenu. `ew70` : BTC, ETH et LTC à 0,7/3 chacun, achetés le premier jour et détenus (même exposition maximale que la stratégie). w1 est la fenêtre du README, sur laquelle les paramètres ont été réglés ; w2 est hors échantillon.

| Fenêtre | Bras | Sharpe QC | CAGR | Drawdown max | PSR |
|---|---|---|---|---|---|
| w1 2018-2024 | `legacy` (publié) | 0.798 | 24.99 % | 57.1 % | 19.2 % |
| w1 | `entries` (corrigé) | 0.415 | 8.30 % | 37.3 % | 5.2 % |
| w1 | `btc` détenu | 1.075 | 39.28 % | 76.4 % | 30.4 % |
| w1 | `ew70` détenu | 0.717 | 22.09 % | 71.2 % | 14.5 % |
| w2 2025 → 2026-07-01 | `legacy` | -0.636 | -10.73 % | 29.7 % | 1.9 % |
| w2 | `entries` | -0.572 | -8.79 % | 29.8 % | 2.3 % |
| w2 | `btc` détenu | -0.489 | -24.31 % | 52.0 % | 3.1 % |
| w2 | `ew70` détenu | -0.604 | -23.62 % | 47.0 % | 2.1 % |

Statistiques d'exécution des deux bras de la stratégie :

| Fenêtre | Bras | Jours de filtre actif | dont avec une ligne détenue | Clôtures sous le stop sans sortie | Sorties sur stop | Dépassement max au déclenchement |
|---|---|---|---|---|---|---|
| w1 | `legacy` | 1603 | 1206 | 699 | 69 | 22,9 % |
| w1 | `entries` | 1603 | 176 | 0 | 78 (dont 36 un jour de filtre) | 18,3 % |
| w2 | `legacy` | 186 | 38 | 61 | 29 | 19,7 % |
| w2 | `entries` | 186 | 5 | 0 | 29 (dont 4 un jour de filtre) | 16,4 % |

Les clôtures sous le stop se comptent par ligne et par jour. Le dépassement est l'écart entre le niveau du stop et la clôture qui le déclenche.

**Ce que la mesure dit.**

- Le filtre n'isole pas des crashs rares : il est actif 1603 jours sur les 2557 de w1. La mesure de volatilité (ATR rapporté au prix, multiplié par √252) dépasse 60 % la plupart du temps en crypto.
- Le rendement publié venait des lignes gardées pendant le filtre : 1206 jours détenus sans surveillance, et 699 clôtures sous le stop restées sans sortie sur w1. Une fois les stops rétablis, le Sharpe de w1 passe de 0.798 à 0.415 et le CAGR de 25,0 % à 8,3 %. Le drawdown descend de 57,1 % à 37,3 %.
- Les gaps n'expliquent pas le drawdown de 57 % : quand les stops sont évalués chaque jour, la clôture qui déclenche un stop est au plus 18,3 % sous son niveau. Le drawdown de la version d'origine venait surtout des stops suspendus.

**Significativité** (`Paradox46Benchmarks/significance.py`, Sharpe à taux nul annualisé par √252, Ledoit-Wolf et bootstrap stationnaire ; Holm sur `btc` et `ew70`, diagnostic `legacy` à part) :

| Fenêtre | `entries` contre | Sharpe `entries` / bras | p Holm Ledoit-Wolf | p Holm bootstrap |
|---|---|---|---|---|
| w1 | `btc` | 0.46 / 0.72 | 1.0 | 1.0 |
| w1 | `ew70` | 0.46 / 0.55 | 1.0 | 1.0 |
| w1 | `legacy` (diagnostic) | 0.46 / 0.62 | 1.0 | 1.0 |
| w2 | `btc` | -0.31 / -0.42 | 1.0 | 1.0 |
| w2 | `ew70` | -0.31 / -0.50 | 1.0 | 1.0 |
| w2 | `legacy` (diagnostic) | -0.31 / -0.38 | 1.0 | 1.0 |

**Verdict.**

- **w2, hors échantillon : pas de BEATS.** Au Sharpe du protocole (taux nul), `entries` est au-dessus de BTC détenu (-0.31 contre -0.42), sans aucune significativité : **INCONCLUSIVE**. Au Sharpe de QC, qui retire le taux sans risque, il est en dessous (-0.572 contre -0.489) et la règle **NO BEATS** se déclencherait. Le protocole ne disait pas lequel des deux Sharpe la règle NO BEATS lisait : les deux lectures sont données. Sur cette fenêtre, la stratégie perd moins que les références en CAGR (-8,8 % contre -24,3 % pour BTC détenu), avec un drawdown de 29,8 % contre 52,0 %.
- **w1, dans l'échantillon (indicatif) :** la stratégie corrigée est sous BTC détenu et sous le panier détenu, écarts non significatifs. La version publiée, elle aussi, était sous BTC détenu (Sharpe 0.798 contre 1.075).

### Lecture honnête

- **CAGR 24,99 % publié** : il mesurait une stratégie qui gardait ses lignes sans stop pendant 1206 jours de filtre actif, soit 47 % des jours de w1. Ce n'était ni de l'alpha ni une sortie défensive, mais une exposition au marché crypto retenue pendant ses phases les plus agitées.
- **Drawdown** : 57,1 % publié, 37,3 % corrigé, contre 76,4 % pour BTC détenu. C'est le seul point où la stratégie fait mieux que BTC détenu sur w1 ; corrigée, elle le réduit encore, au prix des deux tiers du CAGR.
- **PSR** : 19,2 % publié, 5,2 % corrigé. Aucun des deux ne franchit le seuil conventionnel de 50 %.
- **Filtre ATR 60 %** : tel que mesuré, il n'isole pas des régimes extrêmes ; il est actif la majorité du temps. Le comparer à un seuil plus haut serait une autre expérience, avec son propre protocole écrit avant mesure.

**Conclusion honnête** : ne pas présenter le CAGR publié comme de l'alpha. La stratégie corrigée ne bat ni BTC ni le panier détenus sur aucune des deux fenêtres. Son intérêt pédagogique est de montrer comment un `return` mal placé peut fabriquer un backtest flatteur, et pourquoi un chiffre reproduit au centième doit encore être relu contre le code.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Multi-Layer-EMA"`
**QC Cloud :** Déployé comme project 28433748.

## Fichiers

- `main.py` — Stratégie (classe `OptimizedCryptoAlgorithm`).
- `config.json` — Configuration.
- `quantbook.ipynb`, `research.ipynb` — Recherche (analyse des signaux).
- `ml_ema_analysis.png` — Figure d'analyse.

## Concepts enseignés

- **Multi-indicateur avec confirmation** : un croisement EMA seul est bruité ; exiger RSI + Bollinger le filtre.
- **Gate de volatilité ATR** : bloquer les entrées quand la volatilité annualisée dépasse le seuil. Un filtre qui coupe aussi les sorties suspend les stops au pire moment (#23460).
- **Lire la portée d'un `return`** : un `return` en tête de `OnData` saute toute la gestion des positions, pas seulement les entrées. Le compteur `suspended_breaches` mesure ce que la version d'origine laissait passer.
- **Probabilistic Sharpe Ratio (PSR)** : un CAGR élevé sur un actif à forte dérive haussière (crypto) ne prouve pas le skill (PSR 19 % publié, 5 % corrigé).
- **Honnêteté métrique** : un chiffre reproductible n'est pas un chiffre juste. Le Sharpe 0.798 se reproduit au centième, mais il mesurait un code qui ne faisait pas ce que le README décrivait.

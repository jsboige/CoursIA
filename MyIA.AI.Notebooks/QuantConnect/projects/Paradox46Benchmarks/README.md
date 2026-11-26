# Paradox46Benchmarks

**ID projet Cloud :** 37331102 (créé 2026-10-04)

## Description

Benchmarks de comparaison pour l'évaluation de la stratégie 46 (issue #18906,
point 4) : **SPY détenu** (buy & hold) et **60/40** (SPY 60 % / IEF 40 %,
rebalancé mensuellement), même fenêtre 2018-01-01 → 2026-09-25, même modèle de
frais IBKR que la stratégie évaluée (`InteractiveBrokersFeeModel`, identité à
`fee_mult = 1`).

Un seul projet, mode par paramètre de backtest : `mode = "spy"` (défaut) ou
`mode = "6040"`.

## Résultats

> Runs QC Cloud du 2026-10-04, frais IBKR identiques à la stratégie évaluée
> (`fee_mult = 1`), fenêtre 2018-01-01 → 2026-09-25 (2 195 dates).

| Benchmark | Sharpe | CAGR | Pire baisse | Profit net | Orders | ID run |
|---|---:|---:|---:|---:|---:|---|
| SPY détenu (buy & hold) | 0,499 | 13,907 % | 33,600 % | 212,007 % | 1 | `3f8ffd4c12fb0e621eb29feac8dd194a` |
| 60/40 (SPY 60 % / IEF 40 %, mensuel) | 0,383 | 8,858 % | 21,200 % | 109,950 % | 173 | `54418ac625203c9cad5f7e8afade7578` |

## Significativité de l'écart (#20388)

Question : l'avance de la stratégie 46 sans levier (`universe_mode = "unlevered"`) sur ces deux benchmarks se distingue-t-elle du hasard ?

### Trace d'équité journalière

Les benchmarks (`main.py`) et la stratégie tracent, à chaque séance de SPY, la valeur du portefeuille dans le graphique `shadow`. La séance k va dans la série `e{k % 5}` ; les séries `fees` et `turnover` complètent la trace. C'est le contrat de rejeu en ombre de #18923, lu par `shadow_replay.qc_daily_equity`. La sonde ne prend aucune décision : les profits nets et les nombres d'ordres restent ceux des runs sans sonde (contrôle ci-dessous).

Côté stratégie, la sonde est greffée sur le `main.py` de la v3 de `Paradox46VolScaledMomentum/` par un script rangé avec les traces. Le fichier de la stratégie n'est pas modifié dans le dépôt.

### Tests

`significance.py` lit les trois graphiques et apparie les rendements journaliers ; il refuse le calcul si une séance manque d'un côté. Pour chaque benchmark, il applique trois tests, tous calculés par des organes de `ML-Training-Pipeline/scripts` :

1. écart de Sharpe, avec l'erreur type HAC de Ledoit et Wolf (2008) ;
2. écart de Sharpe par bootstrap stationnaire (bloc moyen de 10 séances, 2 000 tirages, graine 0), avec un intervalle percentile à 95 % ;
3. écart de rendement moyen journalier, avec un t de Newey-West.

Le retard HAC vaut floor(T^0,25), soit 6 ici. Le Sharpe est calculé à taux sans risque nul et annualisé par racine de 252 : il ne recopie donc pas le Sharpe de QC, qui retire le taux sans risque. Les six p-valeurs sont rapportées brutes, puis après correction de Holm. Le bootstrap rend une p unilatérale ; elle est doublée pour être bilatérale comme les deux autres. Ce choix a été fixé après les prédictions, et il ne change pas le verdict : la plus petite p unilatérale vaut 0,28.

`tests/test_significance.py` contient 8 tests CPU, sans Lean ni réseau. Commande, depuis ce dossier : `python -m pytest tests/test_significance.py -q`.

### Résultats

> Runs du 2026-10-16 sur nœuds QC, fenêtre 2018-01-02 → 2026-06-30 (2 134 séances), modèle de frais de la stratégie. Prédictions enregistrées avant les runs : [#20388](https://github.com/jsboige/CoursIA/issues/20388#issuecomment-6210870458).

Contrôle de neutralité de la sonde :

| Run | Profit net | Ordres | Identique au run sans sonde |
|---|---:|---:|---|
| Stratégie 46 sans levier | 277,238 % | 858 | oui |
| SPY détenu | 201,329 % | 1 | oui |
| 60/40 | 108,816 % | 168 | oui |

Tests sur les rendements journaliers appariés :

| | contre SPY | contre 60/40 |
|---|---:|---:|
| Sharpe de la stratégie (taux nul) | 0,930 | 0,930 |
| Sharpe du benchmark (taux nul) | 0,778 | 0,826 |
| Écart de Sharpe | +0,152 | +0,104 |
| Corrélation des rendements | 0,503 | 0,499 |
| Erreur type de l'écart (Ledoit-Wolf) | 0,309 | 0,321 |
| p Ledoit-Wolf | 0,623 | 0,745 |
| IC 95 % bootstrap de l'écart | [−0,464 ; +0,748] | [−0,501 ; +0,702] |
| p bootstrap (bilatérale) | 0,557 | 0,687 |
| Écart de rendement moyen | +1,03 pb/jour | +3,22 pb/jour |
| t et p de l'écart moyen | t = 0,47 ; p = 0,639 | t = 1,64 ; p = 0,100 |

Après correction de Holm, la plus petite p vaut 0,601 (écart moyen contre le 60/40). Aucun test ne rejette à 5 %, ni avant ni après correction.

**Verdict : INCONCLUSIVE, maintenu.** Les prédictions enregistrées avant les runs tiennent toutes. Sur 8,5 ans, l'avance de la stratégie sur SPY et sur le 60/40 reste compatible avec le hasard. Le test le plus proche d'un rejet est l'écart de rendement moyen contre le 60/40 : la stratégie gagne davantage en moyenne, mais elle porte aussi plus de risque, et l'écart de Sharpe correspondant n'est pas significatif.

**Puissance.** Avec une erreur type de 0,31, le plus petit écart de Sharpe détectable (test bilatéral à 5 %, puissance de 80 %) vaut environ 0,87, soit 2,80 × 0,31. C'est plus de cinq fois l'écart observé. À dynamique inchangée, il faudrait un échantillon environ 30 fois plus long pour rendre significatif un écart de 0,15 contre SPY, et environ 75 fois plus long pour un écart de 0,10 contre le 60/40. Ces ordres de grandeur supposent des rendements stationnaires.

Les traces des quatre runs (sources, empreintes, identifiants de backtest, graphiques `shadow`, ordres, journaux, `significance_results.json`) sont conservées hors dépôt, sous `QC-traces/18906-p46-significance/`.

## Comment exécuter

**QC Cloud :** projet 37331102, lancer un backtest avec `mode` = `spy` ou
`6040` (fenêtre par paramètres `start_date` / `end_date`).

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Paradox46Benchmarks"`
(mode SPY par défaut).

## Fichiers

- `main.py` — les deux benchmarks (mode par paramètre), avec la trace d'équité `shadow`
- `significance.py` — les trois tests de significativité de l'écart
- `tests/test_significance.py` — tests CPU de `significance.py`
- `config.json` — identifiants Cloud

## Voir aussi

- `Paradox46VolScaledMomentum/` — la stratégie évaluée
- Issue #18906

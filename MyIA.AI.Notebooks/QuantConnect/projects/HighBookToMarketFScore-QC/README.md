# HighBookToMarketFScore-QC

**Classe d'actifs :** Actions US (value stocks)
**Projets QC :** 29687591 (clone de la bibliothèque, 2026-04-05, cité par `main.py`) · 32732820 (copie cloud de juin 2026 : fenêtre fixe 2018-2025 ; son code, lu le 2026-11-08, ne déclare pas de modèle de courtier) · 39089903 (code du dépôt, mesures du 2026-11-08, espace de backtest du cours) · 39104413 (code de la copie de juin, relancé le 2026-11-08 dans le même espace)

> 🇬🇧 **English version** : voir [`README.en.md`](README.en.md).

## Description

Clone de la **QC Strategy Library #343** (*High Book-to-Market High F-Score Quality Value* par **Louis Szeto**). Stratégie value+quality systématique sélectionnant les actions avec book-to-market élevé filtrées par Piotroski F-Score ≥ 8, equally-weighted, rebalance mensuel.

## Mesures (2026-11-08, #25264)

> **Rappel (#1621, #9434)** : les chiffres 2,09 / 18,44 % / 24,20 % de la docstring de `main.py` sont ceux de la **fiche de bibliothèque**, pas un backtest du dépôt. Le catalogue les a ensuite comparés au Sharpe d'un backtest sur huit ans (0,41) et en a conclu à un effondrement. Les mesures ci-dessous montrent que ces deux nombres ne portent pas sur la même fenêtre.

### Ce que publie la fiche

La fiche #343 affiche des **fenêtres glissantes**, recalculées à chaque lecture : les chiffres changent d'une lecture à l'autre sans que la stratégie change.

| Lecture de la fiche | Sharpe OOS 1 an | CAGR 5 ans | Drawdown max 5 ans | PSR 5 ans | Rendement 3 mois |
|---|---|---|---|---|---|
| 2026-04-05 (docstring de `main.py`) | 2,09 | 18,44 % | 24,20 % | — | — |
| 2026-11-08 (API publique `strategies/read`, `strategyId` 343) | 0,99 | 14,86 % | 28 % | 4,9 % | -8,3 % |

Entre les deux lectures, le Sharpe d'un an est passé de 2,09 à 0,99 : la fenêtre a glissé de sept mois, et le dernier trimestre perd 8,3 %.

### Les cinq backtests

Le code du dépôt accepte deux paramètres, `start` et `end`, qui fixent la fenêtre (voir « Comment exécuter »). Trois runs du 2026-11-08 sur le projet 39089903, la copie cloud de juin pour comparaison, et le code de cette copie relancé le 2026-11-08 :

| Run | Backtest | Lancé le | Fenêtre | Sharpe (QC) | CAGR | Drawdown max | PSR | Ordres | Frais (% du capital initial) |
|---|---|---|---|---|---|---|---|---|---|
| Fenêtre 5 ans de la fiche | `fec0c0b0ea8174206890d3c52b11ed4c` | 2026-11-08 | 2021-08-10 → 2026-08-10 | 0,507 | 17,09 % | 28,0 % | 7,4 % | 1 539 | 2,4 % |
| Fenêtre 1 an de la fiche | `64ac60f2761444e554b6664c7b5c889f` | 2026-11-08 | 2025-08-10 → 2026-08-10 | 1,707 | 43,50 % | 8,2 % | 71,0 % | 262 | 0,5 % |
| Fenêtre fixe 2018-2025 | `90e709b101113920550ef73a0bc5f285` | 2026-11-08 | 2018-01-01 → 2025-12-31 | 0,320 | 10,93 % | 65,0 % | 0,85 % | 2 405 | 3,9 % |
| Copie cloud de juin (projet 32732820) | `26976196c313a99d65f090e0af9d919e` | 2026-06-14 | 2018-01-01 → 2025-12-31 | 0,411 | 14,51 % | 60,4 % | 4,5 % | 2 299 | 5,1 % |
| Code de la copie de juin, relancé (projet 39104413) | `26444efa68228f367c63a1d91719c645` | 2026-11-08 | 2018-01-01 → 2025-12-31 | 0,320 | 10,93 % | 65,0 % | 0,85 % | 2 405 | 3,9 % |

**Fin effective des fenêtres.** L'espace de backtest du cours coupe les backtests 90 jours avant la date du run, sans message d'erreur : les fenêtres 5 ans et 1 an s'arrêtent donc au 2026-08-10, environ trois mois avant celles de la fiche lue le même jour.

**Sharpe.** Le Sharpe de QC retranche un taux sans risque. Recalculé à taux nul sur la courbe de valeur journalière : 0,79 (5 ans), 2,04 (1 an), 0,49 (2018-2025).

**Rendement par année** (courbe de valeur journalière ; 2021 et 2026 partielles) :

| Fenêtre | 2018 | 2019 | 2020 | 2021 | 2022 | 2023 | 2024 | 2025 | 2026 |
|---|---|---|---|---|---|---|---|---|---|
| 2018-2025 | -19,2 % | +14,1 % | +3,0 % | +48,8 % | +4,4 % | +35,4 % | +4,2 % | +9,6 % | — |
| 5 ans (depuis le 2021-08-10) | — | — | — | +2,0 % | +1,8 % | +35,4 % | +4,2 % | +9,9 % | +63,9 % |

Les deux fenêtres ne détiennent pas le même portefeuille au départ : leurs années communes peuvent différer de quelques points (2022), puis se rejoignent (2023, 2024).

**Drawdowns datés** (courbe de valeur journalière) :

- 2018-2025 : -64,0 % du 2018-07-09 au 2020-03-19, regagné le 2021-02-08 (en 2020, l'année perd jusqu'à 56,6 % depuis son plus haut) ;
- 5 ans : -28,0 % du 2024-10-18 au 2025-04-09, regagné le 2025-09-15 ;
- 1 an : -8,2 % du 2025-09-18 au 2025-10-10, regagné le 2025-11-26.

### Lecture

1. **Le 2,09 et le 0,41 ne mesurent pas la même chose.** Le premier est un Sharpe hors échantillon sur un an, lu sur une fiche qui glisse ; le second, un Sharpe sur huit ans. Leur écart ne démontre ni un effondrement ni un surapprentissage de période.
2. **Sur les fenêtres de la fiche, le code du dépôt retrouve l'ordre de grandeur publié.** Drawdown sur 5 ans : 28,0 %, comme la fiche lue le même jour. CAGR sur 5 ans : 17,1 % contre 14,9 % ; la fenêtre de la fiche finit trois mois plus tard, sur un trimestre à -8,3 %. Sharpe sur un an : 1,71 au sens de QC (2,04 à taux nul). Les fenêtres ne coïncident pas : c'est un ordre de grandeur, pas une reproduction au point près.
3. **Le risque est hors des fenêtres de la fiche.** Entre juillet 2018 et mars 2020, la stratégie perd 64 % (repli de la value, puis krach de mars 2020) et ne regagne son plus haut qu'en février 2021. Aucune fenêtre de cinq ans lue en 2026 ne contient cet épisode.
4. **La mesure longue ne permet pas d'affirmer un Sharpe élevé.** Le PSR calculé par QC reste faible sur les fenêtres longues : 7,4 % sur 5 ans, 0,85 % sur 2018-2025 (4,9 % sur la fiche). Seul le run d'un an dépasse 50 %, sur une seule année.
5. **Les frais n'expliquent pas l'écart.** Sur la même fenêtre 2018-2025, la copie de juin, dont le code (lu le 2026-11-08) ne déclare pas de modèle de courtier, a payé plus de frais (5,1 % du capital initial) que le run du 2026-11-08 avec le modèle de courtier déclaré par `main.py` (3,9 %). Le modèle par défaut de LEAN (`DefaultBrokerageModel`, source lue le 2026-11-08) facture déjà les actions avec le barème que déclare `main.py` : les deux runs paient selon le même barème, et l'écart de frais vient de la taille des ordres (moins nombreux, 2 299 contre 2 405, mais passés sur un portefeuille qui a crû plus vite), pas du barème. Le passage à des frais de courtier n'est pas ce qui sépare 2,09 de 0,41.
6. **Le flux de fondamentaux a changé entre les deux runs 2018-2025.** Le 2026-09-23, QuantConnect a migré son historique de fondamentaux Morningstar : environ un tiers des valeurs diffèrent, en général de plus de 20 %. Les ratios, valeurs par action et moyennes sont désormais datés à leur dépôt (médiane : 63 jours après la fin de la période) et non plus à la fin de la période ; d'après la documentation, un backtest qui les lit ne voit plus un chiffre avant qu'il soit public, et les backtests antérieurs ne se reproduisent plus. Le F-Score lit quatre de ces ratios (`operation_ratios.roa`, `current_ratio`, `gross_margin`, `assets_turnover`, horizon `one_year`) et l'univers lit `valuation_ratios.pb_ratio`. La copie de juin lisait l'ancien flux ; sur la même fenêtre, le run du 2026-11-08 perd 3,6 points de CAGR (14,5 % → 10,9 %) et passe d'un Sharpe de 0,41 à 0,32. Le code de la copie de juin, relancé tel quel le 2026-11-08 (projet 39104413), rend exactement le run du dépôt : mêmes statistiques, mêmes 2 405 ordres, mêmes frais, et une courbe de valeur identique point pour point. Le modèle de courtier déclaré par `main.py` ne change donc rien à ce backtest : à code égal, l'écart avec juin vient des données lues entre le 2026-06-14 et le 2026-11-08. La migration des fondamentaux est le changement documenté sur cette période ; ce rejeu ne la sépare pas d'une éventuelle réécriture des prix ajustés.
7. **Le correctif proposé par l'ancienne version de ce README n'existe pas.** `DataNormalizationMode` compte huit membres (`RAW`, `ADJUSTED`, `SPLIT_ADJUSTED`, `TOTAL_RETURN`, `FORWARD_PANAMA_CANAL`, `BACKWARDS_PANAMA_CANAL`, `BACKWARDS_RATIO`, `SCALED_RAW`) ; aucun ne s'appelle `POINT_IN_TIME_FUNDAMENTALS`, et ce mode porte sur les prix, pas sur les fondamentaux. La datation au dépôt est désormais faite par le fournisseur de données (point 6).

### Verdict

Le 2,09 de la fiche n'était pas un Sharpe de long terme, et le 0,41 du catalogue n'est pas un effondrement : ce sont deux fenêtres. Sur les fenêtres de la fiche, le code du dépôt retrouve l'ordre de grandeur publié. Sur huit ans, la stratégie gagne 10,9 % par an, mais elle traverse une perte de 64 % en vingt mois et son PSR reste sous 1 %. Statut : **historique**, avec un profil de risque mesuré. Le recul depuis juin sur 2018-2025 (Sharpe 0,41 → 0,32) ne vient pas du modèle de courtier : le code de juin, relancé le 2026-11-08, rend le même run au point près. Il vient des données, qui ont changé entre les deux dates.

## Comment exécuter

**QC Cloud :** copier `main.py`, `piotroski_score.py`, `piotroski_factors.py`, `universe.py` et `symbol_data.py` dans un projet. Sans paramètre, la fenêtre se termine au 2025-01-01 et commence douze ans avant la date du run (le début glisse avec la date du run). Les paramètres de projet `start` et `end` (format `AAAA-MM-JJ`, les deux ensemble) fixent une fenêtre explicite : par exemple `start = 2021-08-10`, `end = 2026-08-10` pour la fenêtre 5 ans ci-dessus. Les paramètres `score_threshold` (8 par défaut) et `max_universe_size` (100) règlent le filtre F-Score et la taille de l'univers.

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/HighBookToMarketFScore-QC"` ; les mêmes paramètres se déclarent dans la clé `parameters` du `config.json` du projet. Il faut disposer des données de fondamentaux US en local.

## Fichiers

- `main.py` - Stratégie (clone QC Strategy Library #343, Piotroski F-Score value screen monthly rebalance)
- `piotroski_score.py` - Calcul F-Score (Profitabilité + Leverage/Liquidity + Operating Efficiency, 9 signaux binaires)
- `piotroski_factors.py` - Facteurs fondamentaux individuels (ROA, CFO, ΔROA, ACCRUAL, ΔLEVER, ΔLIQUID, EQ_OFFER, ΔMARGIN, ΔTURN)
- `universe.py` - PiotroskiScoreUniverseSelectionModel (sélection universe + filtre F-Score ≥ 8)
- `symbol_data.py` - Helpers pour charger fundamentals data

## Références

- QuantConnect Strategy Library #343 — *High Book-to-Market High F-Score Quality Value* par Louis Szeto : `https://www.quantconnect.com/strategies/343`
- `main.py:5-11` docstring : source library + URL + QC Project ID 29687591 + auteur Louis Szeto
- Documentation QuantConnect, *US Fundamental Data*, section « Migration » (lue le 2026-11-08) : `https://www.quantconnect.com/docs/v2/writing-algorithms/datasets/morningstar/us-fundamental-data`
- Piotroski (2000), « Value Investing: The Use of Historical Financial Statement Information to Separate Winners from Losers », *Journal of Accounting Research* 38(suppl.) — papier fondateur du F-Score
- #25264 — mesures de ce README (fenêtres de la fiche, run 2018-2025, comparaison avec la copie de juin, rejeu de son code)
- c.1281-L3 ★★ (DynamicVIXSpyRegime-QC) — library claim misattribution pattern, arche reproductible pour drainer les autres README QC library clones

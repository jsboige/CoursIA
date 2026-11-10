# AssetClassMomentum-QC

**Asset class:** Multi-Asset (ETF universe)
**Cloud project ID:** 33209767 (`AssetClassMomentum-QC-baseline`)

## Description

Cross-asset ETF momentum rotation, v2.0 consolidée depuis l'article QC research
**#21050** « Cross-Asset ETF Momentum with a Correlation-Based Short Hedge »
(Derek Melchin, 2026-07) — issue #14091, EPIC #11698. Source primaire :
Pauchlyová & Vojtko (2025), *Refining ETF Asset Momentum Strategy*, Quantpedia /
SSRN [5095447](https://ssrn.com/abstract=5095447).

**v2.0 — moteur :**
1. **Univers 13 ETFs** : SPY, IWM, EFA, EEM, IYR, QQQ, LQD, IEF, TIP, GLD, USO,
   DBC, FXE.
2. **Momentum multi-horizon** : moyenne des ROC 3/6/9/12 mois (63/126/189/252 j).
3. **Top-4 en long équipondéré** (25 % chacun), rebalance le 1ᵉʳ jour ouvré du mois.
4. **Hedge court gated par corrélation** : quand la corrélation moyenne des 78
   paires sur 20 j dépasse celle sur 250 j (régime défavorable), short -30 % de
   l'ETF au momentum le plus faible → 130 % brut / 70 % net ; sinon 100 %
   long-only.

v1 (baseline, tranche 3 #1621) : clone QC Strategy Library (5 ETFs, momentum 12 m,
top-3, sans hedge) — Needs-improvement : Sharpe 0.22 / CAGR 6.64 % / MaxDD 28.1 % /
PSR 3.8 % (2018-2025).

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/AssetClassMomentum-QC"`
**QC Cloud:** projet 33209767 — dates paramétrables `start_date` / `end_date`
(défaut 2016-01-01 → 2026-07-01).
**Mesure du 2026-10-27 (#22828) :** voir la section « Verdict contre références
détenues ». Les paramètres `mode`, `start_date` et `end_date` se passent au backtest.

## Backtest Metrics

| Metric | Dev 2016-2021 | OOS 2022-2026 | Full 2016-2026 |
|--------|---------------|---------------|----------------|
| Sharpe Ratio | **0.712** | **0.035** | **0.423** |
| CAGR | 13.596 % | 6.212 % | 10.535 % |
| Max Drawdown | 21.800 % | 19.800 % | 21.800 % |
| Net Profit | 114.996 % ($82 103) | 31.159 % ($29 062) | 186.431 % ($181 895) |
| PSR | 16.961 % | 0.646 % | 0.981 % |

**Verdict honnête** : amélioration nette vs v1 sur la gestion du risque (MaxDD
28.1 % → 21.8 %) et le Sharpe pleine période (0.22 sur 2018-2025 → 0.42 sur
2016-2026), cohérente avec l'article (Sharpe 0.498 vs SPY 0.407 sur 2007-2026).
**Mais l'OOS 2022-2026 ne confirme pas d'edge statistique** (Sharpe 0.035,
PSR 0.65 %) — le régime de taux 2022+ défavorable au momentum cross-asset
frappe aussi la version hedgée. Statut #1621 : Needs-improvement (amélioré,
pas d'edge OOS confirmé).

Le même code, relancé le 2026-10-27 sur 2016-2026, rend un Sharpe QC de 0,44 et un
bénéfice net de 186,470 % (0,423 et 186,431 % dans le tableau ci-dessus) : les prix
ajustés de QC ont bougé entre-temps. La mesure contre références détenues
(section suivante, #22828) remplace ce statut : `NO BEATS` sur les deux fenêtres.

Référence article (#21050, 2007-07 → 2026-06) : Sharpe 0.498 (avec hedge) vs
0.451 (long-only) vs 0.407 (SPY buy-and-hold).

## Verdict contre références détenues (#22828)

Le protocole a été écrit dans #22828 avant le premier backtest, sur le modèle de #21594. Les deux références du verdict, SPY détenu et le 60/40 (SPY 60 %, BND 40 %), tournent dans le même algorithme que la stratégie, sous le même modèle de courtage. Deux diagnostics ne comptent pas dans le verdict :

- `ew13`, les 13 ETF de l'univers à poids égal, rééquilibrés chaque mois : la sélection par momentum ajoute-t-elle quelque chose à la détention de l'univers ?
- `nohedge`, la même règle sans le hedge : le hedge, ajout de la v2.0, ajoute-t-il quelque chose ?

Le paramètre `mode` choisit le portefeuille (`strategy`, `spy`, `6040`, `ew13`, `nohedge`). En mode `strategy`, la décision du code ne change pas.

Propriétés du code, gardées telles quelles :

- quand le hedge est actif, le portefeuille est long de 100 % et court de 30 % au rééquilibrage, sur un compte déclaré sur marge. Entre deux rééquilibrages, l'exposition brute dérive : elle atteint au plus 1,612 sur la fenêtre 1 (début avril 2020 : long 1,139, court 0,474) et 1,374 sur la fenêtre 2 (début février 2026). Le hedge est actif sur 1 530 des 3 289 points quotidiens du graphique d'exposition de QC sur la fenêtre 1, et sur 216 des 548 de la fenêtre 2. Les références sont sans levier ;
- les ordres de la stratégie sont soumis à 8 h, heure de New York, avant l'ouverture, en ordres à l'ouverture (`MarketOnOpen`). Ceux des références partent à 9 h 31 et sont remplis à la clôture (`MarketOnClose`). Aucun ordre n'est passé à minuit ;
- le premier ordre de la stratégie part le 1er février 2016 sur la fenêtre 1, le 3 février 2025 sur la fenêtre 2. Le début de mois de janvier ne produit aucun ordre : la stratégie reste en liquidités pendant le premier mois de chaque fenêtre, alors que les références sont investies dès la première séance. Le protocole annonçait un premier rééquilibrage dès janvier ; la mesure le dément, et le code n'a pas été modifié. L'effet joue dans les deux sens : sur ce premier mois, SPY détenu perd 3,5 % en 2016 et gagne 2,9 % en 2025 ;
- les indicateurs sont préchauffés par `automatic_indicator_warm_up`, sans période de préchauffage ;
- la corrélation se calcule par `history()` sur tous les titres abonnés : en mode `strategy`, les 13 ETF du code. BND n'est abonné qu'en mode `6040`.

Les fenêtres sont coupées au 1er janvier 2025, et non au découpage du tableau « Backtest Metrics » : les paramètres du code (univers, horizons, quatre lignes, hedge de 30 %) viennent de publications de 2025 et 2026, et la fenêtre 2 est la seule qui leur soit postérieure. Elle n'est pas pour autant hors de l'échantillon des sources : la date de fin de leurs données n'a pas été vérifiée.

Les séries comparées sont la valeur du portefeuille à chaque ouverture de SPY. Les tests passent par `Paradox46Benchmarks/significance.py`, avec un taux sans risque nul :

- écart de Sharpe de Ledoit-Wolf ;
- bootstrap stationnaire ;
- écart de moyennes de Newey-West.

Sur chaque fenêtre, la correction de Holm porte sur les six p-valeurs du verdict. Les diagnostics sont une exécution séparée, avec leur propre correction de Holm sur six p-valeurs.

Règle de verdict, écrite avant la mesure :

- `BEATS` : écart de Sharpe positif et significatif (Holm < 0,05, Ledoit-Wolf) contre les deux références ;
- `NO BEATS` : Sharpe de la stratégie inférieur à celui de SPY détenu ;
- `INCONCLUSIVE` : tous les autres cas.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée (2016-01-01 → 2026-07-01), le code instrumenté (`c9684d2b09bfad9f16a5387c6bab1dae`, projet 38506496) reproduit le backtest du code d'origine (`a2c56fc272de5fa96e3b880df7a92b09`, projet 38506493), lancé le même jour :

- 621 ordres sur 621, sans écart de date, de symbole ni de quantité ;
- 27 statistiques QC sur 27, et 8 statistiques d'exécution sur 8.

| Fenêtre | Séances | Sharpe stratégie (taux nul) | SPY détenu (taux nul) | 60/40 (taux nul) | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| 1, 2016-01-04 → 2024-12-31 | 2264 | 0,767 | 0,856 | 0,868 | 1,0 / 1,0 | **NO BEATS** |
| 2, 2025-01-02 → 2026-07-01 | 374 | 0,703 | 1,080 | 1,224 | 1,0 / 1,0 | **NO BEATS** |

Statistiques QC (calculées par QC avec son propre taux sans risque). Leurs Sharpe ne se comparent pas à ceux de la table du dessus : QC retranche un taux sans risque non nul et part de ses propres séries quotidiennes, alors que le protocole prend un taux nul sur la valeur du portefeuille à l'ouverture. Le verdict se lit sur la table du dessus.

| Fenêtre | Mode | Sharpe QC (taux de QC, autre échelle) | CAGR | Pire baisse | Ordres | Backtest |
|---|---|---|---|---|---|---|
| 1 | stratégie | 0,465 | 10,51 % | 21,8 % | 527 | `46b23b6b8607e483221b21709cff63e1` |
| 1 | SPY détenu | 0,588 | 14,53 % | 33,7 % | 2 | `d20feef76234d6d0e0e345883e276672` |
| 1 | 60/40 | 0,487 | 9,35 % | 21,7 % | 180 | `e0babc33c2cbfb371d56e1fffb924487` |
| 1 | 13 ETF à poids égal | 0,327 | 7,16 % | 24,4 % | 612 | `5955c0b00c8e157b8feb459e6b85c99d` |
| 1 | sans hedge | 0,476 | 10,40 % | 23,9 % | 431 | `661e2fab1bad5e9bf309f2a206fce76c` |
| 2 | stratégie | 0,214 | 8,89 % | 14,6 % | 85 | `ae51567f9786bb3c66cacef577d1016c` |
| 2 | SPY détenu | 0,665 | 18,96 % | 18,7 % | 2 | `2e871480e0c462a0c01c1b672b4e630d` |
| 2 | 60/40 | 0,590 | 13,37 % | 11,2 % | 30 | `ce4cc6f98c8d3d03b5466dfcd912e116` |
| 2 | 13 ETF à poids égal | 1,118 | 19,27 % | 9,7 % | 114 | `93453db9be92018414e0c310e5cfab24` |
| 2 | sans hedge | 0,516 | 14,64 % | 14,6 % | 78 | `baf94c84c9f8f53b0b88f7697e7ca65c` |

Le backtest de la fenêtre 2 va jusqu'à sa date codée : sa dernière séance est le 2026-07-01, et la coupure d'environ 90 jours que les nœuds QC utilisés appliquent à la fin des backtests ne l'a pas atteint. Sur ses 374 séances, la fenêtre a peu de puissance.

**Lecture.** Sur les deux fenêtres, la stratégie a un Sharpe ponctuel inférieur à celui de SPY détenu et à celui du 60/40 : `NO BEATS`. Aucun écart n'est significatif : la p de Holm vaut 1,0 pour les six tests de chaque fenêtre. Sur la fenêtre 1, l'intervalle bootstrap à 95 % de l'écart contre SPY détenu va de −0,80 à +0,52 : la mesure ne sépare pas la stratégie de SPY détenu, et rien n'indique qu'elle fasse mieux.

**Diagnostic : le hedge n'ajoute rien de mesurable ; l'apport de la sélection reste ouvert sur la fenêtre 1 et manque sur la fenêtre 2.**

| Fenêtre | Diagnostic | Sharpe du diagnostic (taux nul) | Écart stratégie − diagnostic | Intervalle bootstrap 95 % | p Holm (Ledoit-Wolf) | Corrélation | Lecture |
|---|---|---|---|---|---|---|---|
| 1 | 13 ETF à poids égal | 0,684 | +0,083 | −0,62 à +0,71 | 1,0 | 0,53 | question ouverte |
| 1 | sans hedge | 0,792 | −0,025 | −0,34 à +0,30 | 1,0 | 0,89 | rien de mesurable |
| 2 | 13 ETF à poids égal | 1,905 | −1,202 | −2,65 à −0,12 | 0,35 | 0,74 | rien de mesurable |
| 2 | sans hedge | 1,057 | −0,355 | −0,77 à −0,034 | 0,35 | 0,97 | rien de mesurable |

Sur la fenêtre 1, la stratégie dépasse les 13 ETF détenus à poids égal, sans que l'écart soit significatif : selon la règle écrite avant la mesure, la question reste ouverte. Sur la fenêtre 2, elle fait moins bien que les deux diagnostics. L'intervalle bootstrap exclut zéro dans les deux cas, mais la p de Holm de Ledoit-Wolf (0,35) reste loin du seuil : l'écart n'est pas significatif selon la règle. L'article #21050 mesure le hedge sur 2007-2026 (Sharpe 0,498 avec hedge, 0,451 sans). Les deux fenêtres d'ici commencent en 2016 et ne contiennent pas la crise de 2008 : la mesure ne contredit pas l'article sur sa période. Sur la période du code, le hedge n'ajoute rien de mesurable.

**Prédictions écrites avant la mesure :**

- contrôle d'innocuité tenu : juste ;
- fenêtre 1, `NO BEATS` : juste ;
- diagnostic `nohedge` non significatif sur la fenêtre 1 : juste ;
- diagnostic `ew13` sur la fenêtre 1, Sharpe de la stratégie inférieur ou égal à celui des 13 ETF : faux. Il est supérieur (0,767 contre 0,684), sans que l'écart soit significatif ;
- fenêtre 2 : pas de prédiction.

## Files

- main.py - Strategy v2.0 (consolidation article #21050), avec le paramètre `mode` et la trace `shadow` de la mesure #22828

## References

- QuantConnect research #21050 — Cross-Asset ETF Momentum with a Correlation-Based Short Hedge
- Pauchlyová & Vojtko (2025), Quantpedia / SSRN 5095447
- Issue #14091 (verdict CONSOLIDATION), EPIC #11698

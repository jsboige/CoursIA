# HMM-KMeans-Voting

**Asset class:** US Equities/ETF
**Cloud project ID:** None (local only)

## Description

Ensemble regime detection combining Hidden Markov Models with KMeans clustering. Voting mechanism merges regime labels.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/HMM-KMeans-Voting"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | HMM + KMeans voting |
| Rebalance | Monthly |

## Verdict contre références détenues (#23012)

Le protocole a été écrit dans #23012 avant le premier backtest, sur le modèle de #21594, repris par #22828, #22869, #22923 et #22959. Les deux références du verdict, SPY détenu et le 60/40 (SPY 60 %, BND 40 %), tournent dans le même algorithme que la stratégie, sous le même modèle de courtage. Deux diagnostics ne comptent pas dans le verdict :

- `fixed`, l'allocation `neutral` (SPY 45 %, TLT 30 %, IEF 10 %, GLD 15 %, DJP 0 %) détenue en permanence et rééquilibrée chaque mois : la détection de régime ajoute-t-elle quelque chose à l'allocation intermédiaire ?
- `nocrisis`, la même règle sans le disjoncteur de crise : le disjoncteur ajoute-t-il quelque chose ?

Le paramètre `mode` choisit le portefeuille ; `start_date` et `end_date` choisissent la fenêtre. En mode `strategy`, la décision du code ne change pas. BND n'est pas dans l'univers du code : seul le mode `6040` l'abonne.

Propriétés du code, gardées telles quelles :

- le K-Means a une graine fixe et le HMM s'initialise sur les terciles du rendement : le code est déterministe ;
- l'inférence garde les 30 dernières barres d'un historique de 60 (correctif #20286) et y recalcule les variables. La volatilité et le momentum sur 60 séances y portent donc sur moins de 30 rendements, alors que l'entraînement les calcule sur 60 ;
- la première décision tombe le premier jour de bourse de chaque fenêtre : le 2015-01-02 en régime `bear` sur la fenêtre 1, le 2025-01-02 en régime `neutral` sur la fenêtre 2. Le code décide aussi hors du début de mois, par `on_data`, quand le portefeuille est vide : c'est arrivé une fois, le 2018-10-18, sur la fenêtre 1 ;
- les ordres de la stratégie partent 30 minutes après l'ouverture (rééquilibrage mensuel) ou 60 minutes après (disjoncteur), et sont remplis à la clôture du jour (`MarketOnClose`). Seuls les 4 ordres passés par `on_data` le 2018-10-18, après la clôture, sont remplis à l'ouverture suivante (`MarketOnOpen`). Ceux des références partent une minute après l'ouverture et sont tous remplis à la clôture ;
- DJP, détenu seulement en régime `bear`, a des données jusqu'au 2026-07-01, dernière séance de la fenêtre 2.

### Défaut de rééquilibrage, mesuré dans les journaux d'ordres

Chaque rééquilibrage passe par `liquidate()` puis cinq `set_holdings`. Tous ces ordres sont remplis ensemble à la clôture, et `set_holdings` calcule le sien sur la position encore détenue, sans tenir compte de la vente en attente. La position finale vaut donc la cible moins l'ancienne position. Le protocole de #23012 disait le contraire (« seuls les écarts changent la position ; le nombre d'ordres en est gonflé, pas les frais ») : c'était faux.

Exemple en mode `nocrisis` sur la fenêtre 1, où DJP a un poids cible nul hors régime `bear` : DJP vaut +666 parts le 2015-01-02, −666 le 2015-02-02, +666 le 2015-03-02, −666 le 2015-04-01. Aucun poids de la table n'est négatif, et le portefeuille porte pourtant des positions courtes.

| Backtest | Dates de remplissage avec au moins une position courte | Ordres refusés (`Invalid`) | Ordres annulés |
|---|---|---|---|
| contrôle, code de `main` (2015-01-01 → 2024-01-01) | 128 sur 185 | 46 | 10 |
| stratégie, fenêtre 1 | 138 sur 201 | 46 | 10 |
| sans disjoncteur, fenêtre 1 | 84 sur 120 | 21 | 0 |
| stratégie, fenêtre 2 | 14 sur 26 | 15 | 6 |
| sans disjoncteur, fenêtre 2 | 10 sur 19 | 16 | 0 |

Les ordres annulés portent la balise « Liquidated » : un `liquidate()` les annule avant leur remplissage. Ils n'apparaissent qu'en mode `strategy`, le seul où le disjoncteur passe ses ordres. Les modes `spy`, `6040` et `fixed` passent par `set_holdings` sans `liquidate()` : aucun ordre refusé ni annulé, aucune position courte.

Conséquences pour la lecture :

- le verdict porte sur le code tel qu'il est sur `main`, défaut compris ;
- le diagnostic `fixed` compare la stratégie défectueuse à une allocation correctement détenue : il ne mesure pas l'apport de la détection seule ;
- le diagnostic `nocrisis` mesure le disjoncteur greffé sur un rééquilibrage défectueux, pas le disjoncteur voulu.

Le correctif et la re-mesure font l'objet de #23014. Cette section n'y touche pas : elle mesure le code de `main`.

### Mesure

Les fenêtres sont : fenêtre 1, du 2015-01-01 au 2024-12-31 (elle prolonge d'un an la fenêtre codée, qui s'arrête au 2024-01-01) ; fenêtre 2, du 2025-01-01 au 2026-07-01, postérieure à tout réglage possible des paramètres.

Les séries comparées sont la valeur du portefeuille à chaque ouverture de SPY. Les tests passent par `Paradox46Benchmarks/significance.py`, avec un taux sans risque nul :

- écart de Sharpe de Ledoit-Wolf ;
- bootstrap stationnaire ;
- écart de moyennes de Newey-West.

Sur chaque fenêtre, la correction de Holm porte sur les six p-valeurs du verdict. Les diagnostics sont une exécution séparée, avec leur propre correction de Holm sur six p-valeurs.

Règle de verdict, écrite avant la mesure :

- `BEATS` : écart de Sharpe positif et significatif (Holm < 0,05, Ledoit-Wolf) contre les deux références ;
- `NO BEATS` : Sharpe de la stratégie inférieur à celui de SPY détenu ;
- `INCONCLUSIVE` : tous les autres cas.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée (2015-01-01 → 2024-01-01), le code instrumenté (backtest `ebe98b64ac0fd4ee550d5ed31dce5b29`, projet 38545037) reproduit le backtest du code d'origine (`e2d5880c3709b0468269f2d20b7e78da`, projet 38545034), lancé le même jour :

- 1685 ordres sur 1685, sans écart de date, de symbole ni de quantité ;
- 27 statistiques QC sur 27, et les statistiques d'exécution communes à l'identique (le code instrumenté y ajoute seulement ses compteurs).

Le code d'origine donne, sur sa fenêtre : Sharpe QC −0,567, CAGR −6,84 %, pire baisse 63,2 %, PSR 0 %, rendement net −47,1 %, 1685 ordres. L'ancienne ligne du registre `docs/qc/qc-strategies-status.md` (Sharpe QC 0,488, CAGR 6,99 %, pire baisse 23,8 %, PSR 6,9 %) ne se reproduit pas sur ce code.

| Fenêtre | Séances | Sharpe stratégie (taux nul) | SPY détenu (taux nul) | 60/40 (taux nul) | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| 1, 2015-01-02 → 2024-12-31 | 2516 | −0,536 | 0,786 | 0,802 | 0,0027 / 0,0027 | **NO BEATS** |
| 2, 2025-01-02 → 2026-07-01 | 374 | 0,530 | 1,080 | 1,224 | 1,0 / 1,0 | **NO BEATS** |

Statistiques QC (calculées par QC avec son propre taux sans risque). Leurs Sharpe ne se comparent pas à ceux de la table du dessus : QC retranche un taux sans risque non nul et part de ses propres séries quotidiennes, alors que le protocole prend un taux nul sur la valeur du portefeuille à l'ouverture. Le verdict se lit sur la table du dessus.

| Fenêtre | Mode | Sharpe QC (taux de QC, autre échelle) | CAGR | Pire baisse | Volatilité annuelle (QC) | Ordres | Backtest |
|---|---|---|---|---|---|---|---|
| 1 | stratégie | −0,646 | −7,26 % | 65,2 % | 10,4 % | 1825 | `6935294413295dd190f44bf6149cce7c` |
| 1 | SPY détenu | 0,533 | 12,97 % | 33,7 % | 14,6 % | 1 | `026d5a5a15a096677315a9d794baec4f` |
| 1 | 60/40 | 0,441 | 8,41 % | 21,7 % | 9,0 % | 201 | `80da6805de2984d7da2b0391a1a2b6a6` |
| 1 | `neutral` détenue | 0,390 | 7,08 % | 24,2 % | 7,6 % | 337 | `a05499408d35302fb45a97430f25a42e` |
| 1 | sans disjoncteur | 0,460 | 9,48 % | 23,7 % | 10,6 % | 1100 | `7464da18ec78a0a15b60597913b22284` |
| 2 | stratégie | −0,011 | 5,18 % | 13,8 % | 9,9 % | 222 | `df8e1a77b24b984054cd0d02464e0e53` |
| 2 | SPY détenu | 0,665 | 18,96 % | 18,7 % | 14,7 % | 2 | `75ef08db53bd661ca58382e1e718a000` |
| 2 | 60/40 | 0,590 | 13,37 % | 11,2 % | 9,1 % | 30 | `bda058df4583102cf5d6419e8fc5b897` |
| 2 | `neutral` détenue | 0,710 | 14,68 % | 7,9 % | 8,7 % | 52 | `8ddada2ad411301053fab1263093efd3` |
| 2 | sans disjoncteur | −0,113 | 3,76 % | 15,9 % | 9,7 % | 144 | `af71deac68820fc769a224c2aa1d3696` |

Le backtest de la fenêtre 2 va jusqu'à sa date codée : sa dernière séance est le 2026-07-01, et la coupure d'environ 90 jours que les nœuds QC utilisés appliquent à la fin des backtests ne l'a pas atteint. Sur ses 374 séances, la fenêtre a peu de puissance. Ses deux références reproduisent celles des mesures #22828, #22869, #22923 et #22959, lancées dans d'autres algorithmes : mêmes Sharpe à taux nul, mêmes statistiques QC, à l'arrondi près pour le Sharpe QC du 60/40 sur la fenêtre 1 (0,441 ici, 0,442 dans #22959).

**Lecture.** Sur la fenêtre 1, la stratégie perd de l'argent (Sharpe à taux nul −0,536) quand SPY détenu et le 60/40 en gagnent (0,786 et 0,802) : le verdict est `NO BEATS`, et l'écart est significatif contre les deux références (p de Holm 0,0027 pour Ledoit-Wolf, 0,0016 et 0,0027 pour l'écart de moyennes ; intervalle bootstrap à 95 % de −2,14 à −0,50 contre SPY détenu, de −2,16 à −0,48 contre le 60/40). Sur la fenêtre 2, son Sharpe ponctuel (0,530) est inférieur à celui des deux références (1,080 et 1,224), sans écart significatif (p de Holm 1,0, intervalle bootstrap de −2,33 à +1,02 contre SPY détenu) : le verdict est `NO BEATS`. La stratégie est presque décorrélée de ses références sur la fenêtre 1 (0,04 avec SPY détenu, 0,07 avec le 60/40), et l'est moins sur la fenêtre 2 (0,37 et 0,42).

**Diagnostic : sur la fenêtre 1, la stratégie fait significativement moins bien que l'allocation `neutral` détenue et que sa propre règle sans disjoncteur ; sur la fenêtre 2, rien n'est significatif.**

| Fenêtre | Diagnostic | Sharpe du diagnostic (taux nul) | Écart stratégie − diagnostic | Intervalle bootstrap 95 % | p Holm (Ledoit-Wolf) | Corrélation | Lecture |
|---|---|---|---|---|---|---|---|
| 1 | `neutral` détenue | 0,799 | −1,335 | −2,16 à −0,49 | 0,0074 | 0,18 | significativement moins bien |
| 1 | sans disjoncteur | 0,773 | −1,309 | −2,19 à −0,46 | 0,0074 | 0,09 | significativement moins bien |
| 2 | `neutral` détenue | 1,385 | −0,856 | −2,32 à +0,43 | 1,0 | 0,51 | rien de mesurable |
| 2 | sans disjoncteur | 0,346 | +0,184 | −0,97 à +1,32 | 1,0 | 0,58 | rien de mesurable |

Le disjoncteur s'est déclenché 46 fois sur la fenêtre 1 et 4 fois sur la fenêtre 2. Sur la fenêtre 1, la règle sans disjoncteur a pris 120 décisions mensuelles : 28 `bull`, 59 `neutral`, 33 `bear` (23 %, 49 %, 28 %). La stratégie en a pris 156, rééquilibrages de sortie de crise compris : 29 `bull`, 73 `neutral`, 54 `bear`. Sur la fenêtre 2 : 3, 12 et 4 décisions sans disjoncteur ; 3, 12 et 8 avec. La pire baisse QC de la stratégie dépasse celle de la règle sans disjoncteur sur la fenêtre 1 (65,2 % contre 23,7 %) ; sur la fenêtre 2, elle est plus faible (13,8 % contre 15,9 %).

Ce que ces chiffres disent, et ce qu'ils ne disent pas. La règle sans disjoncteur porte le même défaut de rééquilibrage et reste proche de SPY détenu sur la fenêtre 1 (0,773 contre 0,786) : le défaut seul n'explique pas la perte de la stratégie. Le disjoncteur multiplie les rééquilibrages (1825 ordres contre 1100) et les positions courtes (138 dates sur 201 contre 84 sur 120). L'hypothèse que la perte vient de la combinaison du disjoncteur et du défaut n'est pas mesurée ici : la re-mesure après correctif (#23014) la tranchera.

**Prédictions écrites avant la mesure :**

- contrôle d'innocuité tenu : juste ;
- fenêtre 1, `NO BEATS` : juste ;
- diagnostic `fixed` sur la fenêtre 1, écart non significatif : faux, la stratégie fait significativement moins bien ;
- diagnostic `nocrisis` sur la fenêtre 1, écart non significatif : faux, la stratégie fait significativement moins bien ;
- diagnostic `nocrisis` sur la fenêtre 1, pire baisse QC de la stratégie inférieure à celle de la règle sans disjoncteur : faux (65,2 % contre 23,7 %) ;
- fenêtre 2 : pas de prédiction.

Les séries complètes (traces `shadow`, journaux d'ordres, sorties de `significance.py`) sont hors dépôt : `G:\Mon Drive\MyIA\IA\QC-traces\23012-hmm-kmeans-voting-held-references\`.

## Files

- main.py - Strategy

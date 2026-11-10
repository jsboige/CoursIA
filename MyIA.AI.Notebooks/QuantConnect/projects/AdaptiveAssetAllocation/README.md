# AdaptiveAssetAllocation

**Classe d'actifs :** Actions/ETF US (diversifié)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Top-4 ETFs par momentum 6 mois avec optimisation de portefeuille à variance minimum. Sélection parmi SPY, EFA, EEM, VNQ, GLD, DBC, TLT, IEF, TIP, HYG (10 ETFs, top 4).

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/AdaptiveAssetAllocation"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

**Paramètres de `main.py` (#21747).** Sans paramètre, `main.py` exécute la stratégie sur sa fenêtre codée (2015-01-01 → 2024-12-31). Trois paramètres de backtest servent à la mesurer contre des références détenues, sans toucher à sa décision :

- `mode` : `strategy` (défaut), `spy` (SPY détenu), `6040` (SPY 60 %, BND 40 %) ou `ew10` (les dix titres de l'univers à poids égal). Les références se rééquilibrent le premier jour de cotation de chaque mois, une minute après l'ouverture ; BND n'est abonné qu'en mode `6040` ;
- `start_date` et `end_date` (format `%Y%m%d`) : remplacent les bornes de la fenêtre.

Chaque mode trace aussi `shadow` : la valeur du portefeuille à l'ouverture de chaque séance de SPY, répartie sur les séries e0 à e4 (contrat #18923).

## Métriques du backtest

| Métrique | Valeur |
|----------|--------|
| Méthode | Momentum 6M + variance min. |
| Univers | 10 ETFs (top 4) |
| Rebalancement | Mensuel |

## Mesure contre des références détenues (#21747)

`main.py` est mesuré contre trois références détenues, avec les paramètres décrits plus haut. Les références sont SPY détenu, le 60/40 (SPY 60 %, BND 40 %) et `ew10`, les dix titres de l'univers à poids égal. Le protocole est écrit dans #21747 avant le premier backtest. Chaque backtest tourne sur les nœuds QC. Les tests viennent de `Paradox46Benchmarks/significance.py` (taux sans risque nul) : écart de Sharpe de Ledoit-Wolf, bootstrap stationnaire et écart de moyennes de Newey-West.

- **Verdict.** Il compare la stratégie à SPY détenu et au 60/40, avec une correction de Holm sur six p-valeurs. `BEATS` exige un écart de Sharpe positif et une p de Holm (Ledoit-Wolf) inférieure à 0,05 contre les deux références. `NO BEATS` signifie un Sharpe inférieur à celui de SPY détenu. Tous les autres cas sont `INCONCLUSIVE`.
- **Diagnostic.** `ew10` passe dans une exécution séparée, avec Holm sur trois p-valeurs. Il demande si la sélection ajoute quelque chose à la détention des mêmes dix titres, et ne change pas le verdict.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée, le code instrumenté reproduit le backtest du `main.py` d'origine : 443 ordres sur 443 identiques (date, symbole, quantité) et 27 statistiques QC sur 27. Tous les ordres sont remplis, aucun n'est refusé : il n'y a pas d'emprunt involontaire. Tous sont créés à 10:00, heure de New York, 30 minutes après l'ouverture ; aucun ne l'est à minuit.

Sharpe annualisé de la trace `shadow`, taux sans risque nul. L'écart est celui de la stratégie moins la référence. La fenêtre « après » s'arrête au 2026-07-23 : les nœuds QC ont coupé le backtest demandé jusqu'au 2026-10-21, et la fin a été lue sur la trace.

| Fenêtre | Séances | Stratégie | SPY détenu (écart, p LW, p Holm) | 60/40 (écart, p LW, p Holm) | `ew10`, diagnostic (écart, p LW, p Holm) | Verdict |
|---|---|---|---|---|---|---|
| 2015-01-02 → 2024-12-31 | 2516 | 0,809 | 0,786 (+0,023 ; 0,944 ; 1,0) | 0,802 (+0,007 ; 0,983 ; 1,0) | 0,562 (+0,247 ; 0,404 ; 1,0) | `INCONCLUSIVE` |
| 2025-01-02 → 2026-07-23 | 389 | 1,974 | 1,057 (+0,916 ; 0,191 ; 1,0) | 1,171 (+0,803 ; 0,236 ; 1,0) | 1,816 (+0,158 ; 0,780 ; 1,0) | `INCONCLUSIVE` |

Statistiques QC des mêmes backtests. Le Sharpe QC déduit un taux sans risque, celui de la trace non : les deux tableaux ne se comparent pas colonne à colonne.

| Mode | Fenêtre | Sharpe QC | CAGR | Drawdown max | Ordres |
|---|---|---|---|---|---|
| stratégie | 2015-2024 | 0,379 | 6,73 % | 18,7 % | 443 |
| SPY détenu | 2015-2024 | 0,533 | 12,97 % | 33,7 % | 1 |
| 60/40 | 2015-2024 | 0,442 | 8,41 % | 21,7 % | 201 |
| `ew10` | 2015-2024 | 0,179 | 4,70 % | 19,1 % | 574 |
| stratégie | 2025-01 → 2026-07-23 | 1,225 | 20,42 % | 7,1 % | 62 |
| SPY détenu | 2025-01 → 2026-07-23 | 0,601 | 17,39 % | 18,7 % | 2 |
| 60/40 | 2025-01 → 2026-07-23 | 0,499 | 12,06 % | 11,2 % | 30 |
| `ew10` | 2025-01 → 2026-07-23 | 0,976 | 16,24 % | 7,1 % | 90 |

**Lecture.** Sur la décennie codée, la stratégie rend environ deux fois moins que SPY détenu (6,7 % contre 13,0 % par an), avec un drawdown presque deux fois plus faible (18,7 % contre 33,7 %). Par unité de risque, à taux nul, elle fait jeu égal avec SPY détenu et le 60/40 ; aucun écart n'est mesurable. Après la fenêtre codée, ses écarts de Sharpe sont larges en point, mais 389 séances ne suffisent pas à les distinguer de zéro. Contre `ew10`, la sélection par momentum suivie de la variance minimale fait mieux en point sur les deux fenêtres, sans écart significatif : la question reste ouverte.

**La convention de Sharpe change le classement.** Sous la convention QC, la stratégie reste derrière SPY détenu (0,379 contre 0,533) ; à taux nul, elle le rejoint (0,809 contre 0,786). La stratégie est deux fois moins volatile (écart-type annuel 0,071 contre 0,146) : la même déduction du taux sans risque pèse près de deux fois plus sur son Sharpe. La prédiction `NO BEATS` écrite dans #21747 comparait ces deux conventions, et la mesure l'a réfutée.

La ligne `main.py` 2025-01 → 2026-06 du tableau de la variante Framework (plus bas) est une mesure distincte, sur une fenêtre plus courte.

## Variante Framework

`main_framework.py` et `alpha_model.py` réécrivent la stratégie dans l'Algorithm Framework de QC : `AdaptiveAssetAllocationAlpha` émet chaque mois les poids momentum + variance minimale, `InsightWeightingPortfolioConstructionModel` les convertit en cibles. Pour l'exécuter, téléverser `main_framework.py` sous le nom `main.py`, à côté de `alpha_model.py` (projet QC désigné par `config_framework.json`). Même univers, mêmes fenêtres, même top 4 et même modèle de courtage que `main.py`.

### Correctif #20264 : la variante empruntait sans le vouloir

Deux défauts de mécanique, corrigés dans `alpha_model.py` :

- **Tranche de minuit.** Un avis de dividende arrive seul, dans une tranche de 00:00 sans barre. L'alpha y consommait l'émission du mois : le moment de la décision dépendait du calendrier des dividendes (minuit avant la première séance dans 110 mois sur 120 entre 2015 et 2024, clôture de la première séance dans les 10 autres). Il attend désormais la première tranche du mois qui porte une barre.
- **FLAT sans poids.** `InsightWeightingPortfolioConstructionModel` ignore un insight sans poids : un actif sorti de la sélection gardait sa cible UP précédente et n'était jamais vendu. Le portefeuille accumulait jusqu'à 10 positions, empruntait sur marge (exposition brute jusqu'à 2,06 fois les fonds propres) et voyait 2361 ordres d'achat refusés sur 3874 ordres. Chaque ticker reçoit maintenant un insight à chaque émission : UP avec son poids pour les actifs retenus, FLAT avec un poids nul pour les autres.

Le correctif reprend aussi la requête d'historique doublée de #20286 (demi-séances) et rend la durée des insights explicite : `insight_bars`, comptée en séances par Lean.

Comme dans `main.py`, l'écrêtage des poids négatifs de la variance minimale peut annuler un actif retenu : la stratégie tient de 1 à 4 positions.

### Mesures

Backtests QC, journal des ordres rejoué ; fenêtre 2015-2024 du code, puis fenêtre distincte 2025-01 → 2026-06 qui n'a servi à choisir aucune correction.

| Variante | Fenêtre | Sharpe | CAGR | Drawdown max | Ordres | Achats refusés | Exposition brute max |
|----------|---------|--------|------|--------------|--------|----------------|----------------------|
| Framework avant correctif | 2015-2024 | 0,347 | 6,97 % | 26,0 % | 3874 | 2361 | 2,06 |
| Framework corrigée | 2015-2024 | 0,302 | 6,01 % | 22,2 % | 1588 | 0 | 1,00 |
| `main.py` | 2015-2024 | 0,379 | 6,73 % | 18,7 % | 443 | 0 | 1,00 |
| Framework avant correctif | 2025-01 → 2026-06 | 1,478 | 20,49 % | 3,9 % | 578 | 412 | 2,06 |
| Framework corrigée | 2025-01 → 2026-06 | 0,705 | 13,97 % | 7,0 % | 257 | 0 | 1,00 |
| `main.py` | 2025-01 → 2026-06 | 0,978 | 17,47 % | 7,1 % | 58 | 0 | 1,00 |

**C'est une correction de mécanique, pas une amélioration.** Les chiffres d'avant le correctif portaient un levier involontaire : sur la fenêtre 2025-2026, en marché haussier, la variante empruntait environ une fois ses fonds propres, et ce levier gonflait son rendement. Corrigée, elle ne dépasse jamais 1,0 fois les fonds propres et reste derrière `main.py` sur les deux fenêtres. Deux écarts de construction subsistent, non tranchés ici :

- **Moment d'exécution.** `main.py` décide 30 minutes après l'ouverture du premier jour du mois et passe des ordres à la clôture du jour même. La variante Framework décide sur la barre journalière, à la clôture, et ses ordres s'exécutent à la séance suivante.
- **Rééquilibrage de dérive.** Le modèle de construction rééquilibre chaque jour vers les cibles (1588 ordres contre 443). Un bras qui ne rééquilibre qu'aux changements d'insights (`InsightWeightingPortfolioConstructionModel(lambda time: None)`) donne Sharpe 0,305, CAGR 6,05 % et drawdown 22,3 % avec 602 ordres et des frais divisés par 1,8 : ces ordres quotidiens ne changent presque rien au résultat. Mesure descriptive, le code garde le comportement par défaut.

**Point ouvert.** Un insight remplacé reste actif jusqu'à son expiration, et cette expiration déclenche un rééquilibrage. Dans le bras mensuel, les dix ordres créés à 00:00 tombent tous 30 séances après l'avant-dernière émission. La durée des insights déplace donc quelques petits ordres : avec 30 et 45 séances, 46 et 51 ordres diffèrent (une part d'écart ou une date décalée) sur environ 1590, pour un résultat identique au millième près. Dans le bras par défaut, il ne reste qu'un ordre créé à minuit en dix ans (2 parts, 33 séances après l'avant-dernière émission, donc pas une expiration ; vraisemblablement un rééquilibrage de dérive), contre 508 avant le correctif.

## Recherche

`quantbook.ipynb` — QuantBook d'étude de la stratégie AAA (exécution via QC Cloud) : chargement des données 2008-2026 (cycle complet incluant une crise), implémentation momentum + min-variance, balayage des trois paramètres (Top N, période de momentum, fenêtre de volatilité), comparaison aux benchmarks SPY/QQQ et visualisations. Il conclut sur les paramètres retenus dans `main.py` (top 4, momentum 126 jours, volatilité 60 jours). Son univers d'étude est élargi aux large-cap US (commentaire « Docker data availability » dans le notebook) ; la stratégie déployée (`main.py`) reste sur les 10 ETFs ci-dessus.

## Fichiers

- main.py - Stratégie (iter2c, allocation adaptative)
- main_framework.py - Variante Algorithm Framework, à téléverser comme `main.py` du projet de `config_framework.json`
- alpha_model.py - Modèle alpha de la variante Framework
- config_framework.json - Projet QC de la variante Framework
- tests/test_alpha_model.py - Tests CPU de l'alpha, sans Lean ni réseau : `python -m pytest tests/test_alpha_model.py -q`
- quantbook.ipynb - QuantBook de recherche : sweeps de paramètres, benchmarks, verdict

## Références

- Butler, Philbrick, Gordillo (2012), Adaptive Asset Allocation: A Primer, SSRN 2328254

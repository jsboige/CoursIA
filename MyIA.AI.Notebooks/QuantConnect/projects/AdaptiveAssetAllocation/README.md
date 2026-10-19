# AdaptiveAssetAllocation

**Classe d'actifs :** Actions/ETF US (diversifié)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Top-4 ETFs par momentum 6 mois avec optimisation de portefeuille à variance minimum. Sélection parmi SPY, EFA, EEM, VNQ, GLD, DBC, TLT, IEF, TIP, HYG (10 ETFs, top 4).

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/AdaptiveAssetAllocation"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques du backtest

| Métrique | Valeur |
|----------|--------|
| Méthode | Momentum 6M + variance min. |
| Univers | 10 ETFs (top 4) |
| Rebalancement | Mensuel |

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

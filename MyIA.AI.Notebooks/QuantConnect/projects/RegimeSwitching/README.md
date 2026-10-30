# RegimeSwitching

**Classe d'actifs :** Actions/ETF américains
**ID projet Cloud :** Aucun (local uniquement)

## Description

Bascule entre momentum et retour à la moyenne selon un régime lu sur SPY (SMA50 et SMA200). L'univers comprend SPY, QQQ, IEF et GLD.

- **Régime haussier** (SPY au-dessus de sa SMA200 et SMA50 au-dessus de la SMA200) : momentum ajusté du risque sur 63 séances. Le meilleur de SPY/QQQ prend 70 %, l'autre 30 %, et IEF et GLD sont vendus.
- **Régime baissier ou de range** : retour à la moyenne.
  - Un titre risqué dont le RSI(14) passe sous 30 est acheté (30 % répartis), avec GLD et IEF à 35 % chacun.
  - Sans titre survendu, un titre risqué dont le RSI repasse au-dessus de 50 est vendu. GLD et IEF passent alors à 50 % chacun en régime baissier, ou GLD 35 %, IEF 35 % et SPY 30 % en range.

Le rééquilibrage a lieu chaque début de mois, et à chaque changement de régime (contrôle quotidien). Un stop suiveur de −10 % s'applique aux titres risqués, et un écart de poids inférieur à 5 points n'est pas négocié.

## Comment lancer

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/RegimeSwitching"`
**QC Cloud :** pas de projet cloud persistant. Les backtests ci-dessous ont tourné dans des projets de mesure ; copier `main.py` dans un nouveau projet QC Cloud pour relancer.

**Paramètres** (#23221) :

| Paramètre | Valeurs | Défaut |
|-----------|---------|--------|
| `mode` | `strategy` (la stratégie) ; `spy` (SPY 100 % détenu) ; `6040` (SPY 60 % / BND 40 %) ; `ew4` (SPY, QQQ, IEF, GLD à poids égal) | `strategy` |
| `fix` | `on` (les deux correctifs ci-dessous) ; `room` (premier correctif seul) ; `off` (code d'origine) | `on` |
| `start_date`, `end_date` | dates `AAAA-MM-JJ` | `2015-01-01`, `2024-12-31` |

Les trois modes de référence se rééquilibrent le premier jour de bourse du mois, 30 minutes après l'ouverture, à l'heure du rééquilibrage mensuel de la stratégie. Le graphique `shadow` trace la valeur du portefeuille à chaque ouverture de séance de SPY ; c'est l'entrée du calcul de significativité (`Paradox46Benchmarks/significance.py`). Les statistiques d'exécution `gross_max`, `gross_max_day`, `gross_over_1005` et `gross_months` mesurent l'exposition brute (somme des valeurs absolues des positions rapportée à la valeur du portefeuille), lue à chaque ouverture.

## Correction de l'exécution (#23221)

Le compte est déclaré sur marge (`AccountType.MARGIN`) : Lean exécute en empruntant tout ordre qui dépasse les liquidités. La stratégie ne déclare pourtant aucun levier. Deux défauts de la branche de retour à la moyenne en créaient.

**1. Le panier défensif s'ajoutait aux titres risqués conservés.** Les poids de GLD et IEF supposaient la poche risquée vide. Or un titre risqué dont le RSI est entre 30 et 50 n'est pas vendu, et un titre non survendu n'est pas redimensionné quand l'autre l'est. SPY et QQQ pouvaient ainsi rester détenus ensemble (poche risquée à 1,0), avec GLD et IEF à 0,5 chacun par-dessus. Sur 2015-2024, le code d'origine atteint une exposition brute de **1,981** (2016-01-20), avec 224 séances au-dessus de 1,005 réparties sur 22 mois.

Le correctif `room` ramène le panier défensif à la place laissée par la poche risquée. La poche risquée comprend les titres survendus achetés ce jour et les titres risqués conservés à leur poids courant. Les poids défensifs nominaux sont multipliés par min(1, place / somme des poids nominaux).

**2. SPY était vendu puis racheté le même jour.** En range sans titre survendu, SPY est vendu en entier quand son RSI dépasse 50 (`liquidate`), puis remis à 30 % par `set_holdings`. En résolution journalière, les deux ordres se remplissent à la même clôture, et `set_holdings` calcule sa quantité sur la position encore détenue : il revend la différence une seconde fois. Le 2018-11-30, SPY finit à **−252 parts** dans le code d'origine, une position à découvert. Ce défaut était masqué par le premier : avec le correctif `room` seul, le maximum d'exposition reste à 1,090 (2018-12-03), et SPY finit à −234 parts le même jour. C'est le mécanisme mesuré sur MeanReversion (#23199).

Le correctif `on` ajoute au premier : un titre risqué qui sort sur RSI > 50 alors que le panier du jour le vise de nouveau (SPY en range) n'est plus liquidé, et `set_holdings` le ramène seul à son poids.

Les règles de signal (régime, RSI, momentum), le stop, le seuil de 5 points et la cadence ne changent pas.

**Ce que mesure le rejeu des ordres remplis :**

| Bras | Exposition brute max (jour) | Séances > 1,005 | Positions à découvert | Ventes et achats du même titre le même jour |
|------|-----------------------------|-----------------|-----------------------|----------------------------------------------|
| w1, `fix=off` (code d'origine) | 1,981 (2016-01-20) | 224 (22 mois) | 1 (SPY, 2018-11-30) | 0 (deux ventes le 2018-11-30) |
| w1, `fix=room` | 1,090 (2018-12-03) | 46 (6 mois) | 1 (SPY, 2018-11-30) | 4 |
| **w1, `fix=on`** | **1,016 (2023-03-02)** | **43 (5 mois)** | **0** | **0** |
| w2, `fix=off` | 1,318 (2025-04-07) | 49 (6 mois) | 0 | 0 |
| w2, `fix=room` | 1,012 (2025-01-15) | 20 (2 mois) | 0 | 0 |
| **w2, `fix=on`** | **1,012 (2025-01-15)** | **20 (2 mois)** | **0** | **0** |

Le résidu de `fix=on`, au plus 1,6 % au-dessus de 1, n'a pas été attribué ordre par ordre. Il n'implique ni position courte ni double ordre. Il est compatible avec le seuil de 5 points, qui peut laisser une ligne un peu au-dessus de sa cible, et avec le remplissage à la clôture d'ordres dimensionnés plus tôt dans la séance.

**Contrôle d'innocuité.** Sur sa fenêtre codée, le code de `main` d'avant cette PR a tourné sans modification. Le code de cette PR a tourné en `fix=off` sur la même fenêtre, le même jour. Les deux journaux sont identiques : 263 ordres sur 263 (date, symbole, quantité, statut), et aucune statistique QC ne diffère.

## Métriques du backtest

Backtests QC Cloud du 2026-10-29, capital de départ 100 000, frais de courtage modélisés par Lean. La stratégie retenue est le code de cette PR en `fix=on` (`main.py` sha256 `dd78d4640e34`) ; les références sont le même code en `mode` `spy`, `6040` et `ew4`. Résultats lus après `completed: true`.

**w1 : 2015-01-01 → 2024-12-31** (2516 dates négociables)

| Bras | Sharpe QC | CAGR | Drawdown max | PSR | Profit net | Ordres |
|------|-----------|------|--------------|-----|------------|--------|
| **`strategy`, `fix=on`** | **0.556** | **11.95 %** | **26.2 %** | 3.7 % | 209.4 % | 259 |
| `strategy`, `fix=off` (code d'origine) | 0.596 | 12.97 % | 26.3 % | 5.1 % | 239.0 % | 263 |
| `spy` (référence) | 0.542 | 13.18 % | 33.7 % | 3.3 % | 245.1 % | 2 |
| `6040` (référence) | 0.454 | 8.55 % | 21.4 % | 1.6 % | 127.3 % | 202 |
| `ew4` (diagnostic) | 0.611 | 10.38 % | 21.6 % | 5.7 % | 168.7 % | 372 |

**w2 : 2025-01-01 → 2026-07-01** (374 dates négociables, dernière séance le 2026-06-30)

| Bras | Sharpe QC | CAGR | Drawdown max | PSR | Profit net | Ordres |
|------|-----------|------|--------------|-----|------------|--------|
| **`strategy`, `fix=on`** | **0.275** | **9.96 %** | **15.1 %** | 13.7 % | 15.3 % | 39 |
| `strategy`, `fix=off` (code d'origine) | 0.285 | 10.23 % | 15.7 % | 14.0 % | 15.7 % | 41 |
| `spy` (référence) | 0.619 | 17.89 % | 18.6 % | 25.6 % | 28.0 % | 2 |
| `6040` (référence) | 0.548 | 12.80 % | 11.2 % | 22.9 % | 19.8 % | 25 |
| `ew4` (diagnostic) | 0.978 | 20.73 % | 9.7 % | 43.3 % | 32.6 % | 47 |

Le Sharpe de QC retire un taux sans risque. Les tests ci-dessous utilisent un Sharpe à taux nul, calculé sur les rendements journaliers du graphique `shadow`.

**Significativité** (Ledoit-Wolf, bootstrap stationnaire, Newey-West). La correction de Holm porte d'un côté sur les deux références du verdict, de l'autre sur le diagnostic :

| Fenêtre | Comparaison | Sharpe à taux nul (stratégie / bras) | p de Holm, écart de Sharpe (Ledoit-Wolf ; bootstrap) |
|---------|-------------|---------------------------------------|------------------------------------------------------|
| w1 | vs `spy` | 0.86 / 0.80 | 1.0 ; 1.0 |
| w1 | vs `6040` | 0.86 / 0.82 | 1.0 ; 1.0 |
| w1 | vs `ew4` | 0.86 / 1.01 | 1.0 ; 1.0 |
| w2 | vs `spy` | 0.69 / 1.01 | 1.0 ; 1.0 |
| w2 | vs `6040` | 0.69 / 1.16 | 1.0 ; 1.0 |
| w2 | vs `ew4` | 0.69 / 1.55 | 0.29 ; 0.31 |

## Verdict : NO BEATS hors échantillon (2025-2026), INCONCLUSIVE dans l'échantillon (2015-2024)

Le protocole (#23012, repris dans #23221) donne BEATS seulement si l'écart de Sharpe est positif **et** reste significatif après Holm contre les deux références. Il donne NO BEATS si le Sharpe est inférieur à celui du SPY détenu, et INCONCLUSIVE sinon. La fenêtre codée est 2015-2024 : w1 est dans l'échantillon de tout réglage, son verdict n'est qu'indicatif. C'est w2, postérieure, qui tranche ; avec 373 séances, sa puissance est faible.

- **w2 (2025 → mi-2026) : NO BEATS.** Sharpe 0.275 contre 0.619 pour SPY détenu, CAGR 10,0 % contre 17,9 %. Le Sharpe à taux nul est lui aussi sous celui des trois bras (0,69 contre 1,01 pour SPY).
- **w1 (2015-2024) : INCONCLUSIVE.** Sharpe 0.556 contre 0.542 pour SPY détenu, mais l'écart n'est pas significatif après Holm (p = 1,0 contre les deux références). La stratégie rend moins que SPY (CAGR 11,9 % contre 13,2 %) ; son drawdown est plus faible (26,2 % contre 33,7 %).

**Ce que mesure le diagnostic `ew4`.** Les quatre titres de l'univers à poids égal, rééquilibrés chaque mois, ont un Sharpe à taux nul supérieur à celui de la stratégie sur les deux fenêtres (1,01 contre 0,86 sur w1, 1,55 contre 0,69 sur w2), sans écart significatif après Holm. La bascule de régime n'ajoute rien de mesurable à la simple détention de son univers.

**Ce que coûte la correction.** Le code d'origine a un Sharpe QC un peu plus élevé (0.596 contre 0.556 sur w1) : il empruntait jusqu'à 98 % du portefeuille, et un levier non déclaré gonfle le rendement d'une période haussière. À taux nul, l'écart est faible (0,90 contre 0,86 sur w1, 0,695 contre 0,695 sur w2 ; corrélation journalière 0,99), et aucun de ces chiffres n'est une mesure de la stratégie telle qu'elle est décrite.

**Ce qui change par rapport aux chiffres publiés.** Le registre citait 4593 jours, un Sharpe de 0.540 et un profit net de 627,9 %. Ces chiffres portent sur une fenêtre d'environ 12,6 ans que le code ne contient pas : il va de 2015 à 2024. Ils n'ont pas été reproduits. La docstring de `main.py` annonçait aussi une transition progressive des poids sur trois jours et un filtre causal, jamais implémentés : ces mentions sont retirées. Les paramètres ne sont pas re-réglés : un ajustement rétrospectif serait du surapprentissage (EPIC #9768).

## Fichiers

- `main.py` - Stratégie (iter3, bascule de régime ; exposition corrigée par #23221, modes de référence)
- `quantbook.ipynb` - QuantBook de recherche : analyse de la stratégie RegimeSwitching

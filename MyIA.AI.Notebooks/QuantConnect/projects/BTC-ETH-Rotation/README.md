# BTC-ETH-Rotation

**Classe d'actifs :** Crypto (BTC, ETH)
**ID projet Cloud :** 37602829 (mesure #20189, aucun déploiement)

## Description

La stratégie reste toujours investie : chaque lundi, elle place 99 % de sa valeur dans l'actif dont le rendement sur les 28 dernières barres journalières est le plus fort, BTC ou ETH. Elle n'a pas de jambe de liquidités : elle choisit entre deux actifs volatils, sans jamais sortir du marché.

La question posée est l'inverse de celle des stratégies de tendance crypto du dépôt, comme [EMA-Cross-Crypto](../EMA-Cross-Crypto/), qui sortent en liquidités quand le signal se retourne. Ici, on se demande si la **force relative** entre deux actifs corrélés suffit à battre leur simple détention.

`main.py` accepte des paramètres optionnels :

| Paramètre | Défaut | Rôle |
|---|---|---|
| `start` / `end` | `2017-01-01` / `2026-06-30` | dates de la fenêtre |
| `lookback` | `28` | nombre de barres du rendement comparé |
| `review` | `weekly` | revue chaque lundi (`weekly`) ou chaque jour (`daily`) |
| `mode` | `stronger` | `weaker` détient l'actif le plus faible (contrôle) |
| `fee_mult` | `1` | multiplie les frais du modèle de courtier |

Le graphique `shadow` suit le format de la ligue de stratégies (#19821). Il porte une valeur par jour dans des séries entrelacées : `e0`..`e4` pour la valeur du portefeuille, `b0`..`b4` et `h0`..`h4` pour les clôtures de BTCUSD et d'ETHUSD. Les compteurs de fin de run (bascules, jours par actif, frais, première barre reçue) sont publiés en statistiques d'exécution.

## Mesure QC Cloud (#20189) — 2026-10-10, verdict NO BEATS

Cette mesure exécute `main.py` dans le moteur Lean de QC Cloud. Elle suit le protocole commun de la ligue de stratégies (#19821), avec une règle inscrite dans le corps de #20189 avant le premier backtest.

**Données.** La règle demande la place de marché dont l'historique journalier des deux paires en USD est le plus long. Une sonde lancée le 2026-10-10 sur quatre places a retenu **Bitfinex** : ETHUSD y commence le 2016-03-09 et BTCUSD le 2013-01-14. Les frais sont ceux du modèle de courtier Bitfinex de Lean. Le run reçoit 3503 barres journalières pour chaque actif, du 2016-11-28 (début du préchauffage) au 2026-06-30, sans jour manquant. La première décision tombe le lundi 2017-01-02. La candidate et ses références sont comparées du 2017-01-03 au 2026-06-30, soit 3466 jours.

**Protocole.**
- Références : (a) BTC détenu ; (b) 50/50 BTC/ETH rééquilibré chaque lundi. Les deux sont calculées sans frais, sur les clôtures tracées par la candidate.
- Statistique : différence de Sharpe à taux sans risque nul, annualisée sur 365 jours.
- Test : bootstrap circulaire par blocs de 21 jours (10 000 tirages, graine 18921), correction de Holm sur les deux références.

| Run | Sharpe | CAGR | Pire baisse |
|---|---|---|---|
| `base` (candidate) | 1,20 | 90,3 % | −84,0 % |
| BTC détenu | 0,97 | 53,2 % | −82,9 % |
| 50/50 rééquilibré le lundi | 1,10 | 71,7 % | −87,5 % |
| ETH détenu (descriptif) | 1,06 | 73,4 % | −93,8 % |

| Différence de Sharpe | Écart | IC 95 % | p | p Holm | 2017-2019 | 2020-2022 | 2023 → 2026-06 |
|---|---|---|---|---|---|---|---|
| `base` − BTC détenu | +0,23 | [−0,20 ; 0,68] | 0,16 | 0,32 | +0,41 | +0,50 | −0,40 |
| `base` − 50/50 | +0,10 | [−0,17 ; 0,35] | 0,25 | 0,32 | +0,16 | +0,16 | −0,10 |

**Verdict : NO BEATS.** L'écart est positif contre les deux références, mais il n'est significatif contre aucune. La règle exclut alors la grille de paramètres et le run à frais doublés. La rotation a gagné sur 2017-2022 et perdu sur 2023 → 2026-06 contre les deux références. Le rendement annuel est élevé (90,3 %), mais la pire baisse aussi (−84,0 %) : toujours investie, la stratégie subit chaque krach crypto en entier, quel que soit l'actif détenu.

QC affiche un Sharpe de 2,01 et un PSR de 69,4 %. Ce Sharpe suit la convention de calcul propre à QC et n'entre pas dans le protocole.

**Compteurs.** La stratégie a fait 102 bascules, soit environ une toutes les cinq semaines. Elle a passé 1962 jours dans BTC, 1505 dans ETH, et 2 jours en liquidités avant la première décision. Elle a passé 205 ordres : un achat initial, puis une vente et un achat par bascule.

**Contrôle descriptif, hors verdict.** Le run `weaker` détient chaque lundi l'actif le plus faible, sur le même calendrier. Ses jours dans BTC et dans ETH sont ceux de `base`, inversés.

| Run | Sharpe | CAGR | Pire baisse |
|---|---|---|---|
| `weaker` | 0,70 | 27,3 % | −93,0 % |

| Différence de Sharpe | Écart | IC 95 % | 2017-2019 | 2020-2022 | 2023 → 2026-06 |
|---|---|---|---|---|---|
| `base` − `weaker` | +0,49 | de −0,026 à 1,04 | +0,77 | +0,54 | +0,06 |

Le signal de force relative sépare nettement les deux actifs sur 2017-2022, puis presque plus sur 2023 → 2026-06. Cet écart est observé sur la fenêtre même de la mesure : il ne vaut pas règle.

**Corrélation hebdomadaire** de `base` : 0,76 avec BTC et 0,88 avec ETH ; BTC et ETH entre eux : 0,66. La corrélation avec les autres membres de la ligue sera calculée par `scripts/league_correlation.py` (#20083) une fois cet outil disponible sur `main`.

Les traces des runs (plans, empreintes, graphiques, statistiques, positions fermées, `results.json`) sont conservées hors dépôt, sous `QC-traces/20189-btc-eth-rotation/`.

## Exercices de lecture

1. Le run `weaker` passe exactement les jours BTC de `base` dans ETH, et inversement. Pourquoi est-ce une conséquence directe du code, et que contrôle cette symétrie ?
2. La pire baisse de `base` (−84,0 %) est proche de celle du BTC détenu (−82,9 %). Quelle propriété de la règle l'explique, et quelle jambe faudrait-il ajouter pour la réduire ?
3. L'écart `base` − BTC détenu change de signe sur la dernière sous-période. Que faudrait-il mesurer, et sur quelle fenêtre, pour savoir s'il s'agit d'un changement de régime ou d'un tirage défavorable ?

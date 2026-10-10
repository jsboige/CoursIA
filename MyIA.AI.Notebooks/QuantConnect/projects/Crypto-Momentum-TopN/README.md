# Crypto-Momentum-TopN

**Classe d'actifs :** Crypto (panier de 11 cryptomonnaies en USD)
**ID projet Cloud :** 37609460 (mesure #20214, aucun déploiement)

## Description

Chaque lundi, la stratégie classe les actifs d'un panier de cryptomonnaies par leur rendement sur les `L` dernières barres journalières. Elle retient les `N` plus forts et détient chacun à 99 % / `N` de sa valeur, **à condition que son rendement soit positif**. Sinon, la part correspondante reste en liquidités (USD).

C'est le momentum **en coupe** : la stratégie compare des actifs entre eux à une même date. Le dépôt contient déjà deux autres formes de stratégie crypto :
- la tendance sur un seul actif, qui sort en liquidités ([EMA-Cross-Crypto](../EMA-Cross-Crypto/)) ;
- la rotation entre deux actifs, toujours investie ([BTC-ETH-Rotation](../BTC-ETH-Rotation/)).

Ici, la question porte sur un panier entier : détenir chaque semaine les plus forts bat-il BTC détenu, ou le panier entier détenu à parts égales ?

`main.py` accepte des paramètres optionnels :

| Paramètre | Défaut | Rôle |
|---|---|---|
| `start` / `end` | `2018-01-01` / `2026-06-30` | dates de la fenêtre |
| `lookback` | `28` | `L`, nombre de barres du rendement comparé |
| `top_n` | `3` | `N`, nombre d'actifs retenus |
| `mode` | `top` | `bottom` (les `N` plus faibles, même filtre), `nofilter` (les `N` plus forts sans filtre de tendance), `probe` (sonde des données, aucun ordre) |
| `fee_mult` | `1` | multiplie les frais du modèle de courtier |

Le graphique `shadow` suit le format de la ligue de stratégies (#19821). Il porte une valeur par jour dans des séries entrelacées :
- `e0`..`e4` : valeur du portefeuille ;
- `b0`..`b4` : clôture de BTCUSD ;
- `w0`..`w4` : un indice du panier équipondéré, rééquilibré chaque lundi et calculé sans frais dans l'algorithme.

Les compteurs de fin de run sont publiés en statistiques d'exécution : panier, première barre par actif, revues, jours entièrement en liquidités, nombre moyen de lignes détenues.

## Mesure QC Cloud (#20214) — 2026-10-10, verdict NO BEATS

Cette mesure exécute `main.py` dans le moteur Lean de QC Cloud. Elle suit le protocole commun de la ligue de stratégies (#19821). La règle a été inscrite dans le corps de #20214 avant le premier backtest. Elle sépare une **période de développement**, où se choisissent les paramètres, d'une **période hors échantillon**, la seule qui porte le verdict : sans période hors échantillon distincte, un verdict BEATS ne peut pas se poser (arbitrage c.6092954192 sur la PR #19599).

### Données et panier

Place de marché : **Bitfinex**, paires en USD, barres journalières, frais du modèle de courtier Bitfinex de Lean. La liste des candidates a été fixée avant toute mesure : les plus grosses cryptomonnaies du début 2018 cotées en USD sur Bitfinex. Une sonde lancée le 2026-10-10, sans remplissage des jours vides, a relevé la première et la dernière barre de chaque paire sur QC.

Entrent au panier les paires qui ont des barres du 2017-11-01 au 2026-06-30. Onze paires remplissent la condition : BTC, ETH, XRP, LTC, EOS, ETC, XMR, ZEC, DASH, NEO, IOTA.

Quatre paires sont exclues :

| Paire | Motif |
|---|---|
| BCH | Bitfinex a changé de ticker après la scission de 2020. Le premier ticker que Lean résout, `BCHNUSD`, commence le 2020-11-15. La sonde ne chaîne pas les tickers successifs |
| TRX | première barre le 2018-02-02 |
| XLM | première barre le 2018-05-02 |
| OMG | dernière barre le 2025-07-16 |

**Biais du survivant, déclaré.** OMG est exclue parce qu'elle disparaît avant la fin de la fenêtre. Ce biais touche autant la candidate que le panier équipondéré, qui porte sur les mêmes onze paires. Face à BTC détenu, en revanche, il favorise la candidate.

**Trous de données.** Sans remplissage, la sonde voit au plus 8 jours sans barre sur BTC, ETH, LTC et ETC. Ce sont exactement les quatre paires cotées avant août 2016, et toutes les paires cotées plus tard ont des trous d'au plus 3 jours. Le trou de 8 jours précède donc, selon toute vraisemblance, la fenêtre de mesure ; sa date n'a pas été relevée. Pendant la stratégie, Lean remplit les jours vides par la dernière clôture.

### Protocole

- **Fenêtre** : runs du 2018-01-01 au 2026-06-30, préchauffage avant. La première décision tombe le lundi 2018-01-01 pour tous les points de grille. La comparaison commence le 2018-01-02.
- **Développement** : du 2018-01-02 au 2021-12-31 (1460 jours).
- **Hors échantillon** : du 2022-01-01 au 2026-06-30 (1642 jours). Chaque point de grille tourne une seule fois sur toute la fenêtre ; ses rendements journaliers sont découpés à ces dates.
- **Grille** : `L` ∈ {14, 28, 56} × `N` ∈ {2, 3}. Le point retenu est celui dont le Sharpe est le plus haut sur la période de développement. En cas d'égalité au centième, la règle prend le `L` le plus long, puis le `N` le plus grand.
- **Références**, sans frais, calculées sur les clôtures que reçoit l'algorithme : (a) BTC détenu ; (b) le panier équipondéré, rééquilibré chaque lundi. Les séries de référence sont identiques d'un run à l'autre, ce que le script d'analyse vérifie.
- **Statistique** : différence de Sharpe à taux sans risque nul, annualisée sur 365 jours.
- **Test** : bootstrap circulaire par blocs de 21 jours (10 000 tirages, graine 18921), correction de Holm sur les deux références, sur la période hors échantillon seulement.
- **BEATS** exige, contre chacune des deux références :
  - une p de Holm inférieure à 0,05 avec une différence positive ;
  - une différence encore positive à frais doublés ;
  - au moins deux sous-périodes hors échantillon positives sur trois ;
  - au moins quatre des cinq autres points de grille positifs hors échantillon.

### Choix du point de grille, sur la période de développement

| Point | Sharpe dév. | Sharpe hors éch. | CAGR hors éch. | Pire baisse hors éch. |
|---|---|---|---|---|
| **`L14N2` (retenu)** | **0,91** | **0,22** | **−9,9 %** | **−84,3 %** |
| `L14N3` | 0,90 | −0,01 | −19,4 % | −85,1 % |
| `L28N2` | 0,50 | 0,42 | 2,8 % | −76,4 % |
| `L28N3` | 0,58 | 0,10 | −14,0 % | −80,6 % |
| `L56N2` | 0,39 | 0,74 | 31,8 % | −74,3 % |
| `L56N3` | 0,55 | 0,59 | 19,4 % | −66,2 % |
| BTC détenu | 0,80 | 0,36 | 5,4 % | −67,0 % |
| Panier équipondéré | 0,54 | 0,14 | −11,7 % | −67,4 % |

Le point retenu est `L14N2` (rendement sur 14 jours, deux actifs). Son Sharpe de développement, 0,91, devance celui de `L14N3` au centième.

### Verdict, sur la période hors échantillon

| Différence de Sharpe de `L14N2` | Écart | IC 95 % | p | p Holm | 2022 | 2023-2024 | 2025 → 2026-06 |
|---|---|---|---|---|---|---|---|
| contre BTC détenu | −0,14 | [−1,24 ; 0,91] | 0,62 | 0,89 | +0,19 | −1,63 | +1,29 |
| contre le panier équipondéré | +0,08 | [−0,67 ; 0,79] | 0,45 | 0,89 | −0,22 | −0,65 | +0,91 |

**Verdict : NO BEATS.** Hors échantillon, `L14N2` fait moins bien que BTC détenu et à peine mieux que le panier équipondéré, sans écart significatif dans un cas comme dans l'autre. La règle exclut alors le run à frais doublés.

Sur la période de développement, à titre descriptif, l'écart était positif contre les deux références : +0,11 contre BTC détenu (p 0,43) et +0,36 contre le panier (p 0,14). Il n'était significatif contre aucune.

**Le classement de la grille s'inverse d'une période à l'autre.** Les deux points en tête sur le développement (`L14N2`, `L14N3`) sont parmi les trois derniers hors échantillon. Le dernier sur le développement (`L56N2`) est le premier hors échantillon, avec +0,38 contre BTC détenu et +0,60 contre le panier. Aucune règle fixée d'avance ne l'aurait choisi : le lire comme le « bon » réglage serait refaire, sur la période hors échantillon, le choix que le découpage a justement pour but d'interdire.

| Point de grille, hors éch. | Contre BTC détenu | Contre le panier |
|---|---|---|
| `L14N3` | −0,37 | −0,15 |
| `L28N2` | +0,06 | +0,28 |
| `L28N3` | −0,26 | −0,04 |
| `L56N2` | +0,38 | +0,60 |
| `L56N3` | +0,24 | +0,46 |

QC affiche pour `L14N2`, sur toute la fenêtre, un Sharpe de 0,72, un CAGR de 15,5 % et une pire baisse de 94,0 %. Ce Sharpe suit la convention de calcul propre à QC et n'entre pas dans le protocole.

### Compteurs

- `L14N2` a fait 444 revues, une par lundi, et passé 1085 ordres.
- Il a passé 493 jours sur 3104 entièrement en liquidités, soit 16 %. Le filtre de tendance n'a donc vidé le portefeuille qu'une petite partie du temps.
- Il a détenu en moyenne 1,55 ligne sur les 2 possibles.

Sur les autres points, les jours en liquidités vont de 493 (`L` = 14) à 549 (`L` = 56).

### Contrôles descriptifs, hors verdict

Deux contrôles tournent au point retenu (`L` = 14, `N` = 2), sur la même fenêtre :
- `bottom` détient les deux actifs **les plus faibles**, avec le même filtre de tendance ;
- `nofilter` détient les deux plus forts **sans** filtre de tendance, donc toujours investi.

| Run | Sharpe dév. | Sharpe hors éch. | CAGR hors éch. | Pire baisse hors éch. | Jours en liquidités | Lignes en moyenne |
|---|---|---|---|---|---|---|
| `L14N2` | 0,91 | 0,22 | −9,9 % | −84,3 % | 493 | 1,55 |
| `bottom` | 0,78 | −0,10 | −6,5 % | −47,3 % | 2236 | 0,47 |
| `nofilter` | 0,64 | 0,026 | −27,3 % | −91,8 % | 1 | 2,00 |

| Différence de Sharpe, hors éch. | Écart | IC 95 % | p | 2022 | 2023-2024 | 2025 → 2026-06 |
|---|---|---|---|---|---|---|
| `L14N2` − `bottom` | +0,33 | [−0,83 ; 1,47] | 0,30 | −0,76 | −0,41 | +2,19 |
| `L14N2` − `nofilter` | +0,20 | [−0,17 ; 0,55] | 0,15 | +0,08 | +0,01 | +0,33 |

Le contrôle `bottom` reste en liquidités 72 % du temps : les actifs les plus faibles ont rarement un rendement positif sur 14 jours, et le filtre les écarte. Sa pire baisse est donc bien plus faible, mais son Sharpe de développement (0,78) reste proche de celui de `L14N2` (0,91). Sur cette période, le classement par force relative ne sépare guère les plus forts des plus faibles une fois le filtre appliqué.

Le filtre de tendance seul améliore `L14N2` sur les trois sous-périodes hors échantillon. L'écart n'est pas significatif et reste descriptif.

**Corrélation hebdomadaire** de `L14N2` hors échantillon : 0,41 avec BTC détenu, 0,70 avec le panier équipondéré. La corrélation avec les autres membres de la ligue sera calculée par `scripts/league_correlation.py` (#20083) une fois cet outil disponible sur `main`.

### Ce que la mesure ne dit pas

- **La pire baisse reste énorme** : −84,3 % hors échantillon et −83,7 % en développement pour `L14N2`. Le filtre de tendance ne protège pas d'une baisse qui commence pendant qu'un actif est détenu : la sortie n'a lieu qu'au lundi suivant, et seulement si le rendement sur `L` jours est devenu négatif.
- **Une période hors échantillon de quatre ans et demi reste courte** pour une classe d'actifs dont le régime change d'une année à l'autre. Les sous-périodes en témoignent : contre BTC détenu, l'écart passe de −1,63 sur 2023-2024 à +1,29 sur 2025 → 2026-06.
- **Le panier est petit et daté.** Les onze paires sont les grosses cryptomonnaies de 2018. Un panier recomposé chaque année selon la capitalisation du moment serait une autre stratégie, et il exigerait des données d'univers que cette mesure n'utilise pas.

Les traces des runs (sonde, plans, empreintes, graphiques, statistiques, `results.json`, script producteur) sont conservées hors dépôt, sous `QC-traces/20214-crypto-momentum-topn/`.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Crypto-Momentum-TopN"`
**QC Cloud :** projet 37609460, avec les paramètres décrits plus haut. `mode=probe` relance la sonde ; sa fenêtre commence par défaut le 2016-01-01.

## Exercices de lecture

1. Le point retenu sur la période de développement est l'un des plus mauvais hors échantillon, et le plus mauvais sur la période de développement est le meilleur hors échantillon. Qu'aurait conclu une mesure sans découpage, qui aurait choisi le point de grille sur toute la fenêtre puis testé ce même point sur toute la fenêtre ?
2. Le panier équipondéré exclut les paires disparues avant 2026, comme la candidate. Pourquoi ce biais du survivant pèse-t-il sur la comparaison avec BTC détenu, mais pas sur la comparaison avec le panier ?
3. Avec `L` = 14, la stratégie passe environ autant de jours en liquidités qu'avec `L` = 56, mais elle change de lignes plus souvent. Quelle grandeur, tirée du journal des ordres, mesurerait ce coût, et comment le comparer d'un point de grille à l'autre alors que la valeur du portefeuille diffère ?

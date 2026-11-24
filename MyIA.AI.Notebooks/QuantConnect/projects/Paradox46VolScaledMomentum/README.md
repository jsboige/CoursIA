# Paradox46VolScaledMomentum

**Classe d'actifs :** ETFs US (indices + secteurs, version levier x3 et équivalents 1x)
**ID projet Cloud :** 37331100 (créé 2026-10-04)

## Description

Évaluation de la stratégie publique **46** « TheOmniscientParadox » (Strategy
Explorer QuantConnect, auteur affiché : Naitik Gupta, Desenyon Trade Club,
v2.0.1 du 31/01/2026, sous-titre « Volatility-Scaled Daily Momentum ETF
Rotation », plus de 80 000 clones affichés) — issue #18906.

**Réimplémentation déclarée depuis la description publique.** Le projet source
(`27869458`) n'est pas lisible par le compte de la flotte (contrôle de
propriété QC) : les règles implémentées sont celles de la fiche, l'univers est
déclaré ci-dessous. L'oracle de vérification reste possible si le code source
arrive.

La question de l'issue n'est pas de reproduire le chiffre affiché (CAGR 5 ans
82,5 %, pire baisse 41 %, Sharpe 1 an 2,13 — non vérifiés), mais : **ce qu'il
reste de la stratégie sans le levier** — un ETF x3 décroît mécaniquement dans
les marchés agités, et une bonne part du rendement affiché peut venir du levier
plutôt que de la sélection.

## Règles implémentées (description publique)

- rotation quotidienne vers **un seul** ETF ;
- score = momentum composite (variations court / moyen / intermédiaire terme)
  divisé par la volatilité récente ;
- filtre de tendance : clôture au-dessus de sa moyenne 50 jours ;
- pénalité RSI (surachat) appliquée au score ;
- passage en liquidités quand le momentum se dégrade.

## Univers déclaré et équivalent 1x

| Levier x3 | Indice / secteur | Équivalent 1x |
|---|---|---|
| UPRO | S&P 500 | SPY |
| TQQQ | Nasdaq-100 | QQQ |
| UDOW | Dow 30 | DIA |
| TECL | Technologie | XLK |
| SOXL | Semiconducteurs | SMH |
| USD | Financiers (déclaré ; en fait semiconducteurs x2, voir ci-dessous) | XLF |

**Écart connu dans cette table** : le ticker `USD` est le ProShares Ultra
Semiconductors (levier x2 sur les semiconducteurs), pas un x3 financier.
L'univers `leveraged` porte donc deux ETF de semiconducteurs (SOXL x3, USD
x2) et aucun financier, face à un univers 1x qui garde XLF. Toutes les
mesures publiées ci-dessous ont été faites avec cet univers ; l'effet de
l'écart sur la comparaison levier / 1x n'est pas mesuré.

La fiche dit l'univers « dominé par des ETF sectoriels et indiciels à effet de
levier » sans le lister : cet univers de six paires est **déclaré**. La
comparaison levier / 1x utilise la même logique, les mêmes paramètres, les
mêmes fenêtres — seuls les tickers changent.

## Choix fixés avant tout calcul (protocole #18906, point 5)

| Paramètre | Base | Variantes de grille |
|---|---|---|
| fenêtres momentum (court/moyen/intermédiaire) | 21/63/126 j | 10/42/84 (rapide) · 42/126/189 (lente) |
| volatilité | écart-type 20 j des rendements quotidiens | — |
| composite | moyenne simple des trois rendements | — |
| tendance | SMA 50 j | 100 j · 200 j |
| pénalité RSI | `score /= 1 + max(0, RSI14 − 70)/20` | — |
| éligibilité | clôture > SMA ET score > 0, sinon liquidités | — |
| allocation | 98 % sur l'argmax, ventes des autres lignes d'abord, complément sous 97 % | — |
| frais | IBKR (`InteractiveBrokersFeeModel`) | multiplicateur x2 |

**Exécution de la rotation (#20388).** La revue tourne 30 minutes après
l'ouverture sur des données journalières : les ordres partent en
`MarketOnClose` et sont remplis à la clôture, dans l'ordre d'envoi. La
rotation calcule la quantité avant les ventes, envoie les ventes d'abord,
vise 98 % du portefeuille (les 2 % en liquide couvrent le contrôle de marge
à l'envoi), déduit les ordres encore ouverts et plafonne l'achat à la marge
libre. Les ordres refusés et les ordres d'appel de marge sont publiés en
statistiques d'exécution `refused` et `margin_calls` : un run sain les a
tous deux à 0.

## Résultats (frais IBKR, fenêtres réelles)

Deux corrections successives, chacune suivie d'un recalcul complet de la
grille. Les mesures antérieures restent publiées, séparées, comme mesures
historiques ; les conclusions ne portent que sur la v3.

- **v2 (#19082)** : la review adjointe a relevé trois défauts de méthode
  dans `_stats` — fenêtres de momentum indexées depuis la fin de
  l'historique (`closes[-1-n]`), rendements quotidiens inversés
  (RSI/volatilité/pénalité de surachat mesurés à l'envers), et, dans le
  projet compagnon, paniers ombres en poids×prix — corrigés au commit
  `1d3584d8` (témoins déterministes avant/après : fenêtre 21 sur rampe
  1→140 : 5,3636 → 0,1765 ; RSI sur hausse monotone : 0 → 100).
- **v3 (#20388)** : la rotation achetait la nouvelle cible par
  `set_holdings(cible, 1.0)` **sans vendre la ligne précédente**. Aucun
  modèle de courtier n'étant fixé, le compte était en marge avec un levier
  actions de 2 : l'achat était financé à crédit, puis refusé faute de marge,
  et seuls les appels de marge vendaient. En univers `leveraged` sur
  2018-01-01 → 2026-06-30 : jusqu'à trois lignes détenues à la fois, au
  moins deux lignes 1 432 jours calendaires sur 3 005, 174 achats refusés,
  192 ordres d'appel de marge. Le levier effectif était donc proche de 2
  pendant près de la moitié de la fenêtre, **y compris en univers `unlevered`**
  (178 achats refusés, 36 ordres d'appel de marge sur 2018-2024) : la
  stratégie mesurée n'était pas celle de la fiche. Corrigé par la rotation
  décrite plus haut.

### Recalcul v3 (rotation corrigée, QC Cloud, 2026-10-15)

> Runs relancés après le correctif #20388 sur des nœuds de backtest QC Cloud
> (projet 37847828 ; benchmarks : projets 37848253 et 37848284, même code que
> `Paradox46Benchmarks/`). Fenêtre arrêtée au **2026-06-30** : ces nœuds ne
> servent pas les 90 derniers jours, la fin diffère donc de celle des mesures
> v1 et v2 (2026-09-25). Chaque run a été relu à `completed: true` avec son
> journal d'ordres : sur les onze, une seule ligne détenue à chaque clôture,
> 0 achat refusé, 0 ordre d'appel de marge.

| Run | Fenêtre | Sharpe | CAGR | Pire baisse | Profit net | Orders | ID run |
|---|---|---:|---:|---:|---:|---:|---|
| 1x (équivalent sans levier) | 2018-01-01 → 2026-06-30 | **0,632** | **16,905 %** | 19,700 % | 277,238 % | 858 | `0c1be9e27d5ee1980457b5fcd800843e` |
| Levier x3 | 2018-01-01 → 2026-06-30 | 0,681 | 31,376 % | **59,600 %** | 917,266 % | 772 | `c24338824f1fd667eab70a97dda9084e` |
| 1x, fenêtre fiche (5 ans) | 2021-10-01 → 2026-06-30 | 0,554 | 17,096 % | 19,700 % | 111,624 % | 446 | `bfbbc87c5b3da08ca45732285145b712` |
| Levier x3, fenêtre fiche (5 ans) | 2021-10-01 → 2026-06-30 | 1,086 | **62,530 %** | 54,100 % | 904,364 % | 399 | `6caf058a3f831994b51376f364ffd11e` |
| 1x, frais x2 | 2018-01-01 → 2026-06-30 | 0,602 | 16,208 % | 19,900 % | 258,525 % | 859 | `dd1fe0fb93631297567781bcc200af7b` |
| 1x, momentum rapide 10/42/84 | 2018-01-01 → 2026-06-30 | 0,610 | 16,171 % | 20,100 % | 257,572 % | 785 | `a471c2c48c535735406fb4848874a2bd` |
| 1x, momentum lent 42/126/189 | 2018-01-01 → 2026-06-30 | 0,490 | 13,449 % | 20,700 % | 192,296 % | 771 | `393ac073ca24c3e865d85e83f855cfcf` |
| 1x, SMA 100 | 2018-01-01 → 2026-06-30 | 0,538 | 15,304 % | 23,800 % | 235,499 % | 773 | `2e7398da6893d8c20c541741efd12018` |
| 1x, SMA 200 | 2018-01-01 → 2026-06-30 | 0,616 | 17,572 % | 24,500 % | 295,909 % | 753 | `4bcb45503c0b27682f2eb62ada75aa00` |
| 1x, sous-période A | 2018-01-01 → 2022-06-30 | 0,545 | 11,824 % | 17,300 % | 65,308 % | 474 | `7fe208f2c0022b1a21320c63bb7db251` |
| 1x, sous-période B | 2022-07-01 → 2026-06-30 | 0,727 | 22,886 % | 14,100 % | 128,126 % | 387 | `7a5471e318899aca91d28f555530646e` |

Benchmarks sur les mêmes fenêtres (purs buy & hold, mêmes frais IBKR) :

| Benchmark | Fenêtre | Sharpe | CAGR | Pire baisse | ID run |
|---|---|---:|---:|---:|---|
| SPY détenu | 2018-01-01 → 2026-06-30 | 0,496 | 13,856 % | 33,600 % | `885bea6b0b699eee8c2fb3ea6e672efa` |
| 60/40 | 2018-01-01 → 2026-06-30 | 0,397 | 9,048 % | 21,200 % | `653697a28e863f06d3a419296ccb3c4d` |
| SPY détenu, sous-période A | 2018-01-01 → 2022-06-30 | 0,344 | 8,528 % | 33,600 % | `dbcdc4a945bb3f9efc496f2e5125a328` |
| 60/40, sous-période A | 2018-01-01 → 2022-06-30 | 0,330 | 6,104 % | 18,900 % | `d9718f07bfa5c21b8ca76a316c3f2ca5` |
| SPY détenu, sous-période B | 2022-07-01 → 2026-06-30 | 0,621 | 17,652 % | 18,700 % | `9c5bd7711b1fcf25c6671d755ae74132` |
| 60/40, sous-période B | 2022-07-01 → 2026-06-30 | 0,353 | 10,630 % | 13,400 % | `ffe78148e8a6b3e402fe6bd3c23bb1ea` |

Lecture v3 :

- **Le correctif change l'ordre de grandeur.** La base 1x passe de
  0,291 / 9,92 % / 45,3 % (v2) à 0,632 / 16,9 % / 19,7 %, sur une fenêtre
  plus courte de trois mois. Le code ne diffère que par la rotation (et la
  publication des compteurs) : la v2 ne mesurait pas la stratégie de la
  fiche.
- **Le signal ne dépend pas des frais** : la base et la variante frais x2
  font toutes deux 461 rotations ; l'écart entre elles (0,632 contre 0,602)
  vient des seuls coûts.
- **Ce qu'il reste sans le levier** : un Sharpe proche (0,632 contre 0,681),
  à peu près la moitié du CAGR (16,9 % contre 31,4 %) et un tiers de la pire
  baisse (19,7 % contre 59,6 %). Le levier n'est plus dominé en rendement,
  mais il ne paie le CAGR qu'en profondeur de baisse.
- **Le chiffre de la fiche reste non reproduit** : sur sa fenêtre de 5 ans,
  le x3 fait 62,5 % de CAGR pour 54,1 % de pire baisse, contre 82,5 % et 41 %
  affichés. La fenêtre mesurée finit au 2026-06-30, trois mois avant celle
  de la fiche.
- **Grille** : base, frais x2 et momentum rapide sont presque confondus
  (Sharpe 0,60-0,63, CAGR 16,2-16,9 %, pire baisse 19,7-20,1 %). Le
  momentum lent est le plus faible (0,490), et les filtres SMA 100 et 200
  creusent la pire baisse (23,8 % et 24,5 %).
- **Sous-périodes** : positives toutes les deux, la seconde plus forte
  (A : 0,545 · B : 0,727).

### Mesures historiques — code v2 (rotation fautive, #20388, remplacées)

| Run | Fenêtre | Sharpe | CAGR | Pire baisse | Profit net | Orders | ID run |
|---|---|---:|---:|---:|---:|---:|---|
| 1x (équivalent sans levier) | 2018-01-01 → 2026-09-25 | **0,291** | **9,920 %** | 45,300 % | 128,540 % | 512 | `71a60f097050ec032241ef35325f4485` |
| Levier x3 | 2018-01-01 → 2026-09-25 | 0,397 | 6,175 % | **84,200 %** | 68,818 % | 651 | `58cdef38fe6d0305857d25832d8d7890` |
| 1x, fenêtre fiche (5 ans) | 2021-10-01 → 2026-09-25 | 0,226 | 9,223 % | 36,800 % | 55,280 % | 274 | `2469cbebb421e474753d018bb72b9fb5` |
| Levier x3, fenêtre fiche (5 ans) | 2021-10-01 → 2026-09-25 | 0,609 | **22,510 %** | 77,500 % | 175,299 % | 321 | `6b0961ace579074348c57ef3511fac70` |
| 1x, frais x2 | 2018-01-01 → 2026-09-25 | 0,391 | 13,433 % | 36,900 % | 200,849 % | 498 | `f9c9f1f2a380f4ee185d09237eab0251` |
| 1x, momentum rapide 10/42/84 | 2018-01-01 → 2026-09-25 | **0,426** | **14,326 %** | 31,100 % | 222,179 % | 456 | `3dfc52636e590f8f1f1743d6eb9c8cb4` |
| 1x, momentum lent 42/126/189 | 2018-01-01 → 2026-09-25 | 0,386 | 13,349 % | 43,200 % | 198,917 % | 462 | `5a4660df999efaf20dcc403bc85f5caf` |
| 1x, SMA 100 | 2018-01-01 → 2026-09-25 | 0,416 | 14,664 % | 46,300 % | 230,615 % | 444 | `8f7f9fb754dcc398b7b5e25429f5f30c` |
| 1x, SMA 200 | 2018-01-01 → 2026-09-25 | 0,500 | 17,145 % | 48,100 % | 298,630 % | 431 | `520e061861b285bf2d68b2a84e8eddf3` |
| 1x, sous-période A | 2018-01-01 → 2022-06-30 | 0,222 | 5,423 % | 32,500 % | 26,810 % | 273 | `0b25c6dd52803c50f4d177ce91a6442b` |
| 1x, sous-période B | 2022-07-01 → 2026-09-25 | 0,306 | 12,774 % | 32,100 % | 66,485 % | 240 | `a76b157ab7079746c0f3f182b7f81881` |

(Runs relancés séquentiellement le 2026-10-04, nœud par nœud selon la
disponibilité du pool de calcul ; la table est complète.)

Lecture v2 (rotation fautive — le levier de fait faussait chaque ligne) :

- **La correction renverse le face-à-face avec SPY** : le noyau 1x perd
  maintenant sur les TROIS axes contre SPY détenu (0,291 vs 0,499 · 9,92 %
  vs 13,91 % · 45,3 % vs 33,6 %) — l'« avantage modeste » de la version v1
  était un artefact des deux défauts de fenêtres et de sens des rendements.
- **Le levier reste dominé** : x3 rend moins que sa jumelle 1x sur la longue
  fenêtre (6,18 % vs 9,92 %) pour 84,2 % de pire baisse ; sur la fenêtre
  favorable de la fiche il multiplie le CAGR (9,22 % → 22,51 %) au prix de
  77,5 % — le chiffre affiché (82,5 %) reste non reproduit.
- **La base reste le point faible de sa propre grille** (0,291 ; rapide
  0,426 · SMA200 0,500), mais **aucune variante ne franchit le bar** :
  SMA200 égalise le Sharpe de SPY (0,500 vs 0,499) avec 48,1 % de pire
  baisse — l'anti-cherry-pick tient dans les deux sens.
- **Sensibilité aux frais non monotone** (x2 : 0,391 > base 0,291) : la
  trajectoire d'equity diverge dès les premiers ordres changés — on y lit
  la sensibilité chaotique de la rotation, pas une hiérarchie de coûts.
- **Sous-périodes faibles toutes les deux** (A : 0,222 · B : 0,306) : aucun
  régime ne porte le résultat.

### Mesures historiques — code v1 (avant correction #19082, remplacées)

> Le code v1 portait aussi la rotation fautive de la v2 (#20388).

> Tous les chiffres de cette section proviennent des runs listés (IDs cités),
> exécutés via QC Cloud le 2026-10-04 sous le code v1 (défauts de fenêtres et
> de sens des rendements décrits ci-dessus). Aucun chiffre de la fiche n'est
> recopié comme mesure.

#### Stratégie 46, runs complets (frais IBKR, QC Cloud, 2026-10-04, code v1)

| Run | Fenêtre | Sharpe | CAGR | Pire baisse | Profit net | Orders | ID run |
|---|---|---:|---:|---:|---:|---:|---|
| 1x (équivalent sans levier) | 2018-01-01 → 2026-09-25 | **0,530** | **17,861 %** | 28,300 % | 320,411 % | 393 | `7f23d7139a0d124a31e7fdfb2e7eb80b` |
| Levier x3 | 2018-01-01 → 2026-09-25 | 0,541 | 16,892 % | **85,700 %** | 291,169 % | 548 | `7a8780dd4cab74fb0558717cdbeea4a5` |
| 1x, fenêtre fiche (5 ans) | 2021-10-01 → 2026-09-25 | 0,503 | 18,251 % | 27,000 % | 130,760 % | 243 | `87fec2f8d25d5c972098c6a6c2c3accf` |
| Levier x3, fenêtre fiche (5 ans) | 2021-10-01 → 2026-09-25 | 0,917 | **49,810 %** | 70,400 % | 650,964 % | 258 | `7e8c00d480942dd31683264727b392ef` |
| 1x, frais x2 | 2018-01-01 → 2026-09-25 | 0,484 | 16,330 % | 34,200 % | 275,027 % | 395 | `2e77b4938e5d452c49ec3e0ab655f7a1` |
| 1x, momentum rapide 10/42/84 | 2018-01-01 → 2026-09-25 | **0,684** | **23,463 %** | 26,800 % | 530,825 % | 365 | `c19c59713588f5426d1518c75b3d5b3f` |
| 1x, momentum lent 42/126/189 | 2018-01-01 → 2026-09-25 | 0,320 | 10,781 % | 41,600 % | 144,662 % | 418 | `772871985f3a1a54cc27edb6a5dfaf6f` |
| 1x, SMA 100 | 2018-01-01 → 2026-09-25 | 0,534 | 19,167 % | 41,300 % | 362,928 % | 365 | `63bb437cdd6f09870686a80a88c2c93b` |
| 1x, SMA 200 | 2018-01-01 → 2026-09-25 | 0,572 | 20,361 % | 43,400 % | 405,044 % | 256 | `fb2f6a79029315c1bbf988117864030e` |
| 1x, sous-période A | 2018-01-01 → 2022-06-30 | 0,498 | 14,516 % | 28,300 % | 83,978 % | 180 | `00a567fff74ea02dfb37df074d44f197` |
| 1x, sous-période B | 2022-07-01 → 2026-09-25 | 0,554 | 20,851 % | 27,000 % | 123,231 % | 213 | `7a93a8774d2caa8e68d05bdb2ae8f55d` |

Lecture (détailée dans le verdict) :

- **Le levier ne survit pas à la longue fenêtre** : même Sharpe (0,541 vs 0,530),
  CAGR plus bas (16,9 % vs 17,9 %), pire baisse 85,7 % — le x3 décroît plus
  vite qu'il n'accélère sur 2018-2026.
- **Sur la fenêtre favorable de la fiche** (5 ans de marché haussier), le levier
  multiplie le CAGR (18,3 % → 49,8 %) pour 70,4 % de pire baisse — le chiffre
  affiché (CAGR 82,5 %) n'est pas reproduit.
- **La base n'est pas l'optimum de sa propre grille** : la variante rapide
  (10/42/84) fait mieux sur les trois axes (Sharpe 0,684, CAGR 23,5 %, baisse
  26,8 %) — preuve anti-cherry-pick que le protocole ne postule pas la
  supériorité des paramètres de la fiche.
- **Sensibilité douce aux frais** (x2 : 0,530 → 0,484) : la rotation quotidienne
  ne fait pas mourir la stratégie sous les frais IBKR.
- **Sous-périodes homogènes** (A : 0,498 · B : 0,554) : pas de régime unique
  portant tout le résultat.

#### Verdict historique (code v1)

**NO BEATS** au bar pré-engagé — mais le noyau 1x « battait SPY détenu sur
les trois axes » (0,530 / 17,861 % / 28,300 % vs 0,499 / 13,907 % / 33,600 %)
et s'arrêtait au seuil du 60/40 sur l'axe risque. La v2 avait renversé ce
face-à-face et conclu que l'avantage venait des défauts de méthode ; la v3
montre que la perte de la v2 venait surtout de la rotation fautive (voir le
verdict).

## Verdict

**INCONCLUSIVE** au bar pré-engagé (battre les DEUX benchmarks — SPY détenu
et 60/40 — sur les TROIS axes : Sharpe, CAGR, pire baisse). Ce verdict
remplace le NO BEATS de la v2, mesuré sur une rotation qui ne vendait pas.

**La base franchit le bar** sur 2018-01-01 → 2026-06-30 :

| | Sharpe | CAGR | Pire baisse | Verdict 1x vs ce bench |
|---|---:|---:|---:|---|
| Stratégie 46 **sans levier** (v3) | 0,632 | 16,905 % | 19,700 % | — |
| SPY détenu | 0,496 | 13,856 % | 33,600 % | 1x meilleur sur les 3 axes |
| 60/40 | 0,397 | 9,048 % | 21,200 % | 1x meilleur sur les 3 axes (pire baisse : 19,7 % < 21,2 %) |

**La robustesse ne tient qu'en partie** : sur les sept runs de grille et de
sous-périodes, trois franchissent aussi le bar complet (frais x2, momentum
rapide, sous-période A). Les quatre autres échouent :

| Run | Axe perdu |
|---|---|
| momentum lent | Sharpe et CAGR face à SPY (0,490 < 0,496 ; 13,4 % < 13,9 %) |
| SMA 100 | pire baisse face au 60/40 (23,8 % > 21,2 %) |
| SMA 200 | pire baisse face au 60/40 (24,5 % > 21,2 %) |
| sous-période B | pire baisse face au 60/40 de la période (14,1 % > 13,4 %) |

Toutes les variantes 1x battent le 60/40 en Sharpe et en CAGR ; l'axe
fragile est la pire baisse face au 60/40, qui se joue à 1-3 points.

**Significativité non mesurée** : la stratégie est déterministe, chaque
configuration ne donne qu'une trajectoire, et aucun test de Diebold-Mariano
ni découpage walk-forward n'a été fait. Un « BEATS » exigerait ces preuves ;
sans elles, le bar franchi par la base reste une observation.

**Le levier** : le x3 bat SPY en Sharpe et en CAGR (0,681 ; 31,4 %) mais
perd sur la pire baisse (59,6 % contre 33,6 %). Sur la fenêtre de la fiche,
il fait 62,5 % de CAGR pour 54,1 % de pire baisse : **le chiffre affiché par
la fiche (CAGR 82,5 %, pire baisse 41 %) n'est pas reproduit**, sur une
fenêtre mesurée qui finit trois mois avant la sienne.

## Comment exécuter

**QC Cloud :** projet 37331100, compiler puis lancer un backtest avec les
paramètres `universe_mode` (`leveraged` / `unlevered`), `start_date`,
`end_date`, et les variantes de grille (`w_short`/`w_medium`/`w_inter`,
`sma_days`, `fee_mult`).

**Lean CLI local :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Paradox46VolScaledMomentum"`
(les paramètres par défaut exécutent la version levier, fenêtre
2018-01-01 → 2026-09-25). Les runs v3 fixent `end_date` à 2026-06-30 : les
nœuds de backtest utilisés ne servent pas les 90 derniers jours.

## Fichiers

- `main.py` — la stratégie (réimplémentation déclarée, univers par paramètre)
- `config.json` — identifiants Cloud

## Voir aussi

- Projet compagnon `Paradox46Benchmarks/` — SPY détenu et 60/40, mêmes frais
- Projet compagnon `Paradox46Correlation/` — corrélations hebdo avec les allocations du dépôt
- Issue #18906 — protocole complet et verdict

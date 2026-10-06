# LeveragedETFMomentum-QC

**Classe d'actifs :** Actions US (ETF à effet de levier)
**ID projet Cloud :** 37445148 (mesure #19587) ; clone d'origine 29687520 (2026-04-04)

> 🇬🇧 **English version** : voir [`README.en.md`](README.en.md). Elle précède la mesure #19587 : la section « Mesure du code de la stratégie » n'existe qu'ici.

## Description

Clone de la stratégie 60 de la Strategy Library QuantConnect (*Leveraged ETF Momentum Allocator*, Grant Forman). Chaque jour, en données journalières, `main.py` place 100 % du capital sur un seul ETF :

- **SPY au-dessus de sa SMA200** : UVXY si le RSI(10) de QQQ dépasse 81 ou celui de SPY dépasse 80, sinon TQQQ (QQQ ×3) ;
- **SPY sous sa SMA200** : un arbre de seuils RSI(10) choisit entre TECL et SPXL (×3 haussiers), UVXY, TECS (×3 baissier) et BSV (obligations courtes). Les seuils sont 30, 74, 84, 31 et 34, combinés aux SMA20 de QQQ et de TQQQ.

Le code tourne avec le modèle de frais du courtier choisi par l'auteur (`SetBrokerageModel`), en compte sur marge, sans levier au-delà de 100 % du capital.

## Mesure du code de la stratégie (#19587) — deux verdicts BEATS

**Ce que le dépôt publiait avant.** Le catalogue et ce README reprenaient les chiffres de la Strategy Library (Sharpe 1,80, CAGR 101 %). Le registre `docs/qc/qc-strategies-status.md` citait un backtest QC (Sharpe 1,779, PSR 79,8 %) et demandait une confirmation qui n'a jamais eu lieu. Ce README signalait aussi un « SUSPECT overfit haussier » sur la fenêtre 2015-2024. Aucun de ces chiffres n'était comparé à une référence, et aucune différence n'était testée.

**Protocole** (règle inscrite sur #19587 avant le premier backtest) : backtests QC sur toute la période où les neuf ETF cotent, 2012-01-01 → 2026-09-25, frais du courtier. La fenêtre inclut donc la baisse de 2022. La candidate `base` (code tel quel) est comparée à SPY et à QQQ détenus, avec les mêmes frais et la même instrumentation. Le test porte sur la différence de Sharpe à taux sans risque nul, par bootstrap circulaire par blocs de 21 séances (10 000 tirages, graine 18921), avec correction de Holm.

`BEATS` exige trois conditions contre une même référence :
- une p Holm inférieure à 0,05 ;
- une différence qui reste positive à frais doublés et sur au moins deux des trois sous-périodes ;
- une différence positive sur au moins 4 des 5 points de la grille.

La grille fait varier la période des RSI (8, 14), celle de la SMA de SPY (150, 250) et celle des SMA courtes (30). Les seuils RSI de l'auteur ne varient pas : ce protocole ne les teste pas.

Deux contrôles descriptifs, hors verdict :
- `sma200` : TQQQ quand SPY est au-dessus de sa SMA200, BSV sinon, sans aucun seuil RSI ;
- `tqqq` : TQQQ détenu.

**Résultats** (séances de clôture du graphique `shadow`, 3703 séances ; Sharpe à taux sans risque nul) :

| Run | Sharpe | CAGR | Pire baisse | Rotation / an | Frais / an | Ordres |
|---|---|---|---|---|---|---|
| `base` (candidate) | 1,50 | 107,1 % | −52,5 % | 35,8 | 1,95 % | 778 |
| SPY détenu | 0,93 | 15,0 % | −33,7 % | 0,1 | 0,00 % | 3 |
| QQQ détenu | 1,00 | 20,1 % | −35,1 % | 0,1 | 0,00 % | 2 |
| `sma200` (contrôle) | 0,90 | 36,3 % | −59,5 % | 8,8 | 0,54 % | 190 |
| `tqqq` (contrôle) | 0,91 | 44,4 % | −81,6 % | 0,1 | 0,03 % | 8 |
| `base`, frais doublés | 1,47 | 103,8 % | −52,8 % | 35,8 | 3,89 % | 775 |
| `orig` : `base` sur 2015-2024 | 1,52 | 117,5 % | −52,6 % | 43,0 | 1,80 % | 632 |

Rotation : valeur échangée cumulée divisée par la valeur du portefeuille. Frais : somme des frais de chaque séance divisés par la valeur du portefeuille la veille, par an. Le portefeuille est multiplié par plusieurs dizaines de milliers sur la fenêtre : rapportés au capital de départ, les frais n'auraient plus de sens.

Statistiques de QC pour `base` : Sharpe 1,68 (calculé avec un taux sans risque), PSR 83,4 %, capacité estimée 260 M$. Le run `orig` redonne l'ordre de grandeur du registre : Sharpe QC 1,76 contre 1,779, PSR 81,3 % contre 79,8 %. L'écart n'a pas été attribué.

| Différence de Sharpe de `base` | Écart | IC 95 % | p Holm | Frais doublés | 2012-2016 | 2017-2021 | 2022 → 2026-09 |
|---|---|---|---|---|---|---|---|
| contre SPY | +0,57 | [0,09 ; 1,02] | 0,012 | +0,54 | −0,05 | +1,02 | +0,56 |
| contre QQQ | +0,50 | [0,12 ; 0,88] | 0,012 | +0,47 | −0,07 | +0,78 | +0,60 |

| Point de grille | Sharpe | Pire baisse | Contre SPY | Contre QQQ |
|---|---|---|---|---|
| RSI 8 | 1,31 | −66,6 % | +0,38 | +0,31 |
| RSI 14 | 1,35 | −59,0 % | +0,42 | +0,35 |
| SMA de SPY 150 | 1,36 | −72,1 % | +0,43 | +0,36 |
| SMA de SPY 250 | 1,17 | −77,8 % | +0,24 | +0,17 |
| SMA courtes 30 | 1,41 | −57,3 % | +0,48 | +0,41 |

**Verdict : BEATS**, contre les deux références. Les deux p Holm valent 0,012. La différence reste positive à frais doublés, sur deux sous-périodes sur trois, et sur les cinq points de la grille. La sous-période 2012-2016 est légèrement négative contre les deux références. Corrélation hebdomadaire avec SPY : 0,41 ; avec QQQ : 0,55.

**Contrôles (descriptifs, hors verdict).**

| Différence de Sharpe | Écart | IC 95 % | 2012-2016 | 2017-2021 | 2022 → 2026-09 |
|---|---|---|---|---|---|
| `base` − `sma200` | +0,59 | [0,28 ; 0,90] | +0,05 | +0,89 | +0,73 |
| `base` − `tqqq` | +0,58 | [0,20 ; 0,97] | −0,04 | +0,83 | +0,76 |

Le filtre de tendance seul (`sma200`) et TQQQ détenu ont un Sharpe voisin de celui de SPY. L'écart avec les références ne vient donc ni du seul levier ni du seul filtre de tendance : il tient aux branches RSI. L'arbre détient TQQQ la plupart du temps : 3390 évaluations sur 4086, contre 225 pour TECL, 184 pour TECS, 144 pour UVXY, 128 pour BSV et 15 pour SPXL. L'arbre est évalué 4086 fois pour 3703 séances, soit parfois plus d'une fois par séance ; la cause n'a pas été recherchée.

**Le résultat de la règle telle qu'elle est écrite (`rule`).** Lean travaille par défaut en prix ajustés. Après les regroupements successifs d'UVXY et de TECS, une part ajustée vaut des centaines de milliers de dollars en début de période. Dans le journal des ordres de `base`, le premier ordre UVXY date du 2017-05-01 (1 part, à 653 000 $) et le premier ordre TECS du 2018-10-23 (11 parts, à environ 185 000 $). Avant ces dates, chaque signal UVXY ou TECS arrondit l'achat à zéro part, et le portefeuille reste en liquide. À l'inverse, une part ajustée de TQQQ vaut quelques centimes : les nombres de parts, donc les frais par part, sont gonflés.

`base` mesure donc la règle telle que QC l'exécute. Le mode `rule` exécute la règle écrite :
- prix bruts, donc des nombres de parts réalistes ;
- mêmes RSI de Wilder et SMA, recalculés chaque jour sur 400 séances d'historique ajusté (paramètres `prices=raw`, `signal=history`).

Ce second verdict a été ajouté au protocole avant tout calcul de verdict (commentaire c.6024690039 sur #19587). Le contrôle `check` (signal recalculé, prix ajustés) redonne la courbe de `base` à l'identique : écart relatif maximal nul, 778 ordres, mêmes comptes d'évaluations. Le signal recalculé est donc bien celui de Lean.

| Run (prix bruts) | Sharpe | CAGR | Pire baisse | Rotation / an | Frais / an | Ordres |
|---|---|---|---|---|---|---|
| `rule` (candidate) | 1,58 | 121,7 % | −50,6 % | 38,7 | 0,60 % | 866 |
| SPY détenu | 0,93 | 15,0 % | −33,6 % | 0,1 | 0,00 % | 61 |
| QQQ détenu | 1,00 | 20,1 % | −35,0 % | 0,1 | 0,00 % | 50 |
| `sma200` (contrôle) | 0,92 | 36,9 % | −59,4 % | 8,8 | 0,08 % | 215 |
| `tqqq` (contrôle) | 0,91 | 44,4 % | −81,6 % | 0,1 | 0,00 % | 20 |
| `rule`, frais doublés | 1,57 | 121,1 % | −50,8 % | 38,6 | 1,14 % | 866 |

QC donne pour `rule` un Sharpe de 1,83 (avec taux sans risque), un PSR de 90,4 % et une capacité estimée de 200 M$.

En prix bruts, SPY et QQQ détenus passent des ordres périodiques, sans doute le réinvestissement des dividendes, versés en liquide dans ce mode (cause non vérifiée dans le journal des ordres). Les frais de `rule` (0,60 % par an) sont plus bas que ceux de `base` (1,95 %) : les nombres de parts n'y sont plus gonflés.

| Différence de Sharpe de `rule` | Écart | IC 95 % | p Holm | Frais doublés | 2012-2016 | 2017-2021 | 2022 → 2026-09 |
|---|---|---|---|---|---|---|---|
| contre SPY | +0,65 | [0,17 ; 1,10] | 0,004 | +0,64 | +0,23 | +1,04 | +0,56 |
| contre QQQ | +0,58 | [0,18 ; 0,97] | 0,004 | +0,57 | +0,20 | +0,80 | +0,60 |

| Différence de Sharpe (descriptive) | Écart | IC 95 % | 2012-2016 | 2017-2021 | 2022 → 2026-09 |
|---|---|---|---|---|---|
| `rule` − `sma200` | +0,66 | [0,34 ; 0,97] | +0,29 | +0,90 | +0,72 |
| `rule` − `tqqq` | +0,66 | [0,27 ; 1,05] | +0,23 | +0,85 | +0,75 |

| Point de grille (prix bruts) | Sharpe | Pire baisse | Contre SPY | Contre QQQ |
|---|---|---|---|---|
| RSI 8 | 1,34 | −66,4 % | +0,41 | +0,34 |
| RSI 14 | 1,33 | −59,0 % | +0,40 | +0,34 |
| SMA de SPY 150 | 1,42 | −72,8 % | +0,49 | +0,42 |
| SMA de SPY 250 | 1,27 | −78,0 % | +0,34 | +0,27 |
| SMA courtes 30 | 1,50 | −55,6 % | +0,57 | +0,50 |

**Second verdict : BEATS.** Contre les deux références, p Holm 0,004. La différence reste positive à frais doublés, sur les trois sous-périodes et sur les cinq points de la grille. Corrélation hebdomadaire avec SPY : 0,38 ; avec QQQ : 0,51. `base` décrit la règle telle que QC l'exécute en prix ajustés ; `rule` décrit la règle écrite.

**Ce que le verdict ne dit pas.**
- **Les seuils ont vu toute la fenêtre.** La Strategy Library date la version 1.0.0 de la stratégie du 31 décembre 2025. Les seuils RSI de l'auteur ont donc pu être réglés sur 2012-2025, et le bootstrap ne corrige pas ce choix. Après la publication, 184 séances seulement (2026-01-02 → 2026-09-25) : `base` y fait un Sharpe de 1,45, contre 1,42 pour SPY et 1,39 pour QQQ, avec une baisse de −31,9 %. C'est trop court pour trancher dans un sens ou dans l'autre.
- **Une année porte une grande part du résultat.** En 2020, `base` multiplie sa valeur par 16 : UVXY prend la hausse de la volatilité de février-mars, puis TQQQ et TECL le rebond. 2020 retirée, la différence de Sharpe reste positive : +0,31 contre SPY et +0,35 contre QQQ pour `base`, +0,41 et +0,44 pour `rule`. Ces quatre écarts sont descriptifs, non testés.
- **La pire baisse vient de la fin 2018, en TQQQ** : −52,5 % entre le 2018-08-29 et le 2018-12-24, sommet retrouvé le 2019-04-15. Sur les mêmes dates, TQQQ détenu perd 58,1 % et QQQ 22,8 %. Sur toute la fenêtre, TQQQ détenu perd jusqu'à −81,6 %.
- **Capacité.** Le portefeuille du backtest est multiplié par environ 45 000 et atteint plusieurs milliards de dollars, bien au-delà de la capacité estimée par QC (200 à 260 M$). Le Sharpe se calcule sur les rendements et ne dépend pas de l'échelle ; le CAGR au-delà de la capacité n'est pas atteignable, et le backtest ne modélise pas l'impact de marché.

**Suivi en ombre.** `base` est gelé à la date du verdict. Son inscription au registre du suivi en ombre (#18923, point 6 du protocole) est faite à part, avec les autres gels en attente.

Les traces des runs (graphiques, statistiques, journal des ordres, empreinte du code envoyé à QC) sont conservées hors dépôt, sous `QC-traces/19587-leveraged-etf-momentum/`.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/LeveragedETFMomentum-QC"`
**QC Cloud :** projet 37445148. Paramètres de backtest :
- `start`, `end` (défauts : 2015-01-01 et 2024-12-31, les dates d'origine du code) ;
- `mode` : `base` (règle d'origine), `sma200`, `tqqq`, `spy` ou `qqq` ;
- `fee_mult` (1 par défaut) ;
- `prices` : `adjusted` (défaut) ou `raw` ; `signal` : `indicators` (défaut) ou `history`. `raw` impose `history` ;
- les périodes de la règle : `rsi_period`, `spy_sma_period`, `qqq_sma_period`, `tqqq_sma_period`.

Avec les défauts, la règle de trading est celle d'origine.

## Fichiers

- `main.py` — stratégie (clone de la stratégie 60 de la Strategy Library), instrumentée pour la mesure #19587

## Références

- QuantConnect Strategy Library, stratégie 60 — *Leveraged ETF Momentum Allocator*, Grant Forman : `https://www.quantconnect.com/strategies/60`
- #19587 — protocole, ajout du second verdict (c.6024690039) et résultats
- #18923 — suivi en ombre des stratégies mesurées
- #19450 — même protocole, appliqué à `LongShortHarvest-QC`

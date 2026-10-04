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
| USD | Financiers | XLF |

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
| frais | IBKR (`InteractiveBrokersFeeModel`) | multiplicateur x2 |

## Résultats (frais IBKR, fenêtres réelles)

> **Recalcul en cours (code v2).** La review adjointe de PR #19082 a relevé
> trois défauts de méthode dans `_stats` — fenêtres de momentum indexées
> depuis la fin de l'historique (`closes[-1-n]`), rendements quotidiens
> inversés (RSI/volatilité/pénalité de surachat mesurés à l'envers), et,
> dans le projet compagnon, paniers ombres en poids×prix — corrigés au
> commit `1d3584d8` (témoins déterministes avant/après : fenêtre 21 sur
> rampe 1→140 : 5,3636 → 0,1765 ; RSI sur hausse monotone : 0 → 100).
> Les runs v1 ci-dessous restent publiés comme **mesures historiques du
> code précédent, explicitement séparées** ; ils sont remplacés run par run
> par les runs v2 relancés le 2026-10-04 (section suivante). Les conclusions
> ne porteront que sur les valeurs v2.

### Recalcul v2 (code corrigé, QC Cloud, lancés le 2026-10-04)

| Run | Fenêtre | Sharpe | CAGR | Pire baisse | Profit net | Orders | ID run |
|---|---|---:|---:|---:|---:|---:|---|
| 1x (équivalent sans levier) | 2018-01-01 → 2026-09-25 | **0,291** | **9,920 %** | 45,300 % | 128,540 % | 512 | `71a60f097050ec032241ef35325f4485` |
| Levier x3 | 2018-01-01 → 2026-09-25 | *(en cours)* | | | | | `58cdef38fe6d0305857d25832d8d7890` |
| 1x, fenêtre fiche (5 ans) | 2021-10-01 → 2026-09-25 | *(en file)* | | | | | — |
| Levier x3, fenêtre fiche (5 ans) | 2021-10-01 → 2026-09-25 | *(en file)* | | | | | — |
| 1x, frais x2 | 2018-01-01 → 2026-09-25 | *(en file)* | | | | | — |
| 1x, momentum rapide 10/42/84 | 2018-01-01 → 2026-09-25 | *(en file)* | | | | | — |
| 1x, momentum lent 42/126/189 | 2018-01-01 → 2026-09-25 | *(en file)* | | | | | — |
| 1x, SMA 100 | 2018-01-01 → 2026-09-25 | *(en file)* | | | | | — |
| 1x, SMA 200 | 2018-01-01 → 2026-09-25 | *(en file)* | | | | | — |
| 1x, sous-période A | 2018-01-01 → 2022-06-30 | *(en file)* | | | | | — |
| 1x, sous-période B | 2022-07-01 → 2026-09-25 | *(en file)* | | | | | — |

(Les runs v2 sont relancés séquentiellement selon la disponibilité des
nœuds de calcul de l'organisation ; les valeurs remplissent ce tableau au
fil des complétions.)

### Mesures historiques — code v1 (avant correction #19082, remplacées)

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

## Verdict

> **Provisoire (code v1).** Ce verdict repose sur les mesures historiques
> ci-dessus ; il est rejoué sur les runs v2 dès leur complétion.

**NO BEATS** au bar pré-engagé (battre les DEUX benchmarks — SPY détenu et
60/40 — sur les TROIS axes : Sharpe, CAGR, pire baisse). Barres de référence
mesurées (runs compagnons `Paradox46Benchmarks/`, mêmes frais IBKR, même
fenêtre 2018-01-01 → 2026-09-25) :

| | Sharpe | CAGR | Pire baisse | Verdict 1x vs ce bench |
|---|---:|---:|---:|---|
| Stratégie 46 **sans levier** | 0,530 | 17,861 % | 28,300 % | — |
| SPY détenu | 0,499 | 13,907 % | 33,600 % | **battu sur les 3 axes** |
| 60/40 | 0,383 | 8,858 % | 21,200 % | battu en Sharpe/CAGR, **pas en pire baisse** (28,3 % > 21,2 %) |

Le noyau sans levier fait donc mieux que SPY détenu sur les trois axes — un
résultat réel mais modeste (écart de Sharpe +0,03, PSR 3,4 % vs 2,9 % :
l'écart n'est pas statistiquement décisif) — et s'arrête au seuil du 60/40 sur
l'axe risque. Deux fragilités mesurées par la grille :

- **frais x2** : le face-à-face avec SPY bascule (Sharpe 0,484 < 0,499, pire
  baisse 34,2 % > 33,6 %) — l'avantage ne survit pas à un doublement des
  frais ;
- **momentum lent** (42/126/189) : perd contre SPY sur les trois axes (0,320 /
  10,8 % / 41,6 %) — la famille momentum de la fiche va de « bat SPY » à
  « perd contre SPY » selon la vitesse choisie, et la base n'en est qu'un
  point.

**Le levier, lui, est dominé** : sur la longue fenêtre la version x3 rend MOINS
que sa propre jumelle 1x (16,9 % vs 17,9 %) pour 85,7 % de pire baisse ; sur la
fenêtre favorable de la fiche il multiplie le CAGR (18,3 % → 49,8 %) au prix de
70,4 % de pire baisse — et **le chiffre affiché par la fiche (CAGR 82,5 %,
pire baisse 41 %) n'est pas reproduit** (49,8 % / 70,4 % mesurés, frais IBKR,
même fenêtre 5 ans).

## Comment exécuter

**QC Cloud :** projet 37331100, compiler puis lancer un backtest avec les
paramètres `universe_mode` (`leveraged` / `unlevered`), `start_date`,
`end_date`, et les variantes de grille (`w_short`/`w_medium`/`w_inter`,
`sma_days`, `fee_mult`).

**Lean CLI local :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Paradox46VolScaledMomentum"`
(les paramètres par défaut exécutent la version levier, fenêtre 2018-2026).

## Fichiers

- `main.py` — la stratégie (réimplémentation déclarée, univers par paramètre)
- `config.json` — identifiants Cloud

## Voir aussi

- Projet compagnon `Paradox46Benchmarks/` — SPY détenu et 60/40, mêmes frais
- Projet compagnon `Paradox46Correlation/` — corrélations hebdo avec les allocations du dépôt
- Issue #18906 — protocole complet et verdict

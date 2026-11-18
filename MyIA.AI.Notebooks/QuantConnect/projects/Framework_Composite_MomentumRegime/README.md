# Framework Composite - MomentumSector + RegimeSwitching

## Description

Stratégie composite combinant deux approches complémentaires via le QuantConnect Algorithm Framework :

1. **SectorMomentum (tranche 60 %)** : Dual momentum entre SPY/IEF/GLD
   - Score composite multi-lookback (1/3/6/12 mois)
   - Filtre SMA200 sur SPY
   - Rééquilibrage mensuel

2. **RegimeSwitching (tranche 40 %)** : Stratégie dépendante du régime
   - Marchés haussiers : Momentum ajusté du risque sur SPY/QQQ (70/30)
   - Marchés baissiers/latéraux : Mean-reversion (RSI survendu) + défensif (GLD/IEF)
   - Détection de régime via SMA50/SMA200 sur SPY

Le modèle de construction de portefeuille (`MultiStrategyPCM`) attribue une part du capital à chaque alpha, puis additionne les deux parts sur les ETF communs. C'est le mode `intent`, par défaut depuis #19740.

**Défaut corrigé par #19740.** Avant d'appeler `determine_target_percent`, le `PortfolioConstructionModel` de Lean ne garde que l'insight actif le plus récent de chaque symbole. Les deux alphas émettent le premier jour de bourse du mois, et l'univers de SectorMomentum (SPY, IEF, GLD) est entièrement inclus dans celui de RegimeSwitching. RegimeSwitching, ajouté en second au `CompositeAlphaModel`, l'emporte donc sur chaque ETF commun : les insights de SectorMomentum n'ont atteint le modèle de construction dans aucun des 403 appels mesurés. Avant #19740, le composite valait donc RegimeSwitching à 40 % et 60 % de liquide :
- exposition brute moyenne 0,40 ;
- corrélation hebdomadaire des rendements avec RegimeSwitching seul : 1,00 ;
- écart de Sharpe avec RegimeSwitching seul : +0,001 [−0,012 ; +0,016].

Ce comportement reste disponible sous `mode` = `base` pour reproduire les chiffres antérieurs. Sous `intent`, le modèle reconstruit les cibles à partir de l'insight actif le plus récent de chaque couple (symbole, alpha), puis les additionne par symbole.

## Fichiers

- `main.py` : Configuration de l'algorithme avec CompositeAlpha et MultiStrategyPouchesPCM
- `alpha_models.py` : Classes SectorMomentumAlpha et RegimeSwitchingAlpha
- `SharedPCM/pouches_pcm.py` (bibliothèque de projet QC) : `MultiStrategyPouchesPCM`, PCM par poches canonique importé par `main.py` (extraction #19821 brique 1)
- `quantbook.ipynb` : QuantBook de recherche du composite Momentum + RegimeSwitching (données natives QC, pré-backtest)

## Non-régression du module partagé (#20188)

Depuis #21134, `main.py` importe `MultiStrategyPouchesPCM` de `SharedPCM/pouches_pcm.py` au lieu de la copie locale `portfolio_construction.py`. Deux backtests QC Cloud du 2026-10-26, aux paramètres par défaut et sur la fenêtre 2015-01-01 → 2025-12-31, vérifient que ce changement ne modifie aucun ordre :

- **A** : le code de `main` au commit `54f9b9eec1`, avec le module partagé ;
- **B** : les mêmes `main.py` et `alpha_models.py`, avec l'ancienne copie `portfolio_construction.py` prise au commit qui précède la migration (`777f502a2a^`). L'argument que l'ancienne copie ne connaît pas (`watch_source="SectorMomentum"`) est retiré de l'appel, et deux propriétés de lecture exposent ses compteurs de diagnostic sous les noms que lit `main.py`.

A et B portent la même instrumentation, qui ne passe aucun ordre. Elle relève la valeur du portefeuille chaque jour à minuit, période de chauffe comprise (252 séances). En fin de backtest, elle calcule une empreinte SHA-256 par année des ordres (identifiant, date, titre, quantité, statut, prix) et des valeurs relevées.

| | A (module partagé) | B (ancienne copie) |
|---|---|---|
| Ordres | 676 | 676 |
| Valeurs relevées | 4 382 | 4 382 |
| Dernière valeur relevée | 238 628,49 | 238 628,49 |
| Sharpe (QC) | 0,353 | 0,353 |
| CAGR | 8,152 % | 8,152 % |
| Pire baisse | 28,3 % | 28,3 % |

Les empreintes annuelles sont égales : 12 sur 12 pour les ordres, 12 sur 12 pour les valeurs. Les 27 statistiques de QC sont égales, rotation comprise. Les compteurs de diagnostic du modèle de construction sont égaux aussi. La migration ne change donc pas le comportement du projet. Traces hors dépôt : `QC-traces/20188-nr/`.

## Performance

### Re-mesure #21349 sur le code de `main` : `NO BEATS`

Backtests QC Cloud du 2026-10-22, code de `main` au commit `7a2d9b84f0`. La fenêtre de verdict (2015-01-02 → 2026-07-09, 2894 séances), la statistique et la règle sont celles de #19740. Le protocole a été écrit sur l'issue avant le premier backtest ([#21349](https://github.com/jsboige/CoursIA/issues/21349), commentaire `c.6329681428`). Depuis #19740, les alphas ont reçu trois correctifs : la tranche de minuit sans barre (#20264) et l'historique court en demi-séance (#20286), dans un même commit, puis l'insight du titre risqué non survendu laissé vivant en survente (#21352).

| Version | Sharpe | CAGR | Pire baisse | Rotation par an | Exposition brute moyenne |
|---------|--------|------|-------------|-----------------|--------------------------|
| `intent` (défaut) | 0,70 | 8,9 % | −28,3 % | 8,6 | 1,00 |
| SectorMomentum seul (`sm`) | 0,48 | 6,6 % | −32,5 % | 7,9 | 1,00 |
| RegimeSwitching seul (`rs`) | 0,87 | 11,9 % | −27,4 % | 9,7 | 1,00 |
| SPY détenu (`spy`) | 0,83 | 13,9 % | −33,7 % | 0,09 | 1,00 |
| 60 % SPY / 40 % IEF (`sixty40`) | 0,89 | 9,0 % | −21,1 % | 0,30 | 1,00 |

**Verdict.** `NO BEATS`, plus net qu'en #19740 : les deux écarts sont négatifs.

| Candidate | Écart avec SPY [IC 95 %] | Écart avec le 60/40 [IC 95 %] | p Holm |
|-----------|--------------------------|-------------------------------|--------|
| `intent` | −0,13 [−0,60 ; +0,30] | −0,19 [−0,63 ; +0,24] | 1,00 |

Comme en #19740, `intent` ne devance les références que sur 2023 → 2026-07 (+0,23 face à SPY, +0,18 face au 60/40) ; il est derrière sur 2015-2018 et 2019-2022. Avec les séances suivantes disponibles (jusqu'au 2026-07-24), les écarts valent −0,14 et −0,19, à titre d'information. La règle ne prévoit les frais doublés et la grille que pour une candidate significative : ils n'ont pas été lancés. `base` n'a pas été re-mesuré.

**Apport de chaque tranche** (écarts descriptifs, hors correction de Holm) : +0,22 [+0,01 ; +0,43] avec SectorMomentum seul, −0,17 [−0,52 ; +0,17] avec RegimeSwitching seul. La lecture de #19740 tient : additionner les tranches améliore SectorMomentum, pas RegimeSwitching.

**D'où vient la baisse de 0,83 à 0,70.** Le témoin, code de #19758 tel que mergé (`8207c650ab`) relancé le même jour, reproduit la série de #19740 : aucune séance ne diffère de plus de 0,01 %. Les données QC n'ont pas bougé, l'écart vient du code. Deux runs ajoutés après lecture du verdict, donc descriptifs, le décomposent par commit :

| Marche de code | Écart de Sharpe [IC 95 %] | Séances qui diffèrent de plus de 0,01 % |
|----------------|---------------------------|-----------------------------------------|
| Extraction du PCM partagé (#21134, `777f502a2a`) | 0,000 | 0 |
| Tranche de minuit et historique court (`e8a077acb0`) | −0,120 [−0,298 ; +0,040] | 483 |
| Titre risqué en survente (#21352) | −0,006 [−0,014 ; +0,000] | 23 |

Les runs ne séparent pas les deux correctifs de `e8a077acb0`. Le correctif d'historique n'agit que lorsque l'historique revient court, ce que #20286 a mesuré en demi-séance ; or la première séance qui diffère, le 2015-02-02, est une séance complète. Une part au moins de l'écart vient donc de la tranche de minuit : un avis de dividende arrivé seul à minuit faisait émettre les alphas sur la clôture de la veille, avec un ordre exécuté à l'ouverture du jour même ; elles émettent désormais toutes à la clôture de la première séance du mois. Aucun intervalle n'exclut zéro. On ne peut pas dire que les correctifs ont dégradé la stratégie, seulement que les chiffres de #19740 ne décrivent plus le code.

**Limites.** Celles de #19740 restent valables : IEF choisi en connaissant la période, fin ramenée par QC Cloud aux 90 derniers jours, sans erreur. Toutes les versions de cette re-mesure ont tourné le même jour, sur les mêmes séances.

### Mesure #19740 : `NO BEATS` (code d'avant les correctifs)

La re-mesure #21349 ci-dessus remplace les lignes `intent`, `sm` et `rs` de cette mesure ; la ligne `base` et la discussion du choix du défaut restent celles du code de l'époque.

Backtests QC Cloud du 2026-10-07, du 2015-01-02 au 2026-07-09 (2894 séances), frais du courtier Interactive Brokers. Le protocole et la règle de verdict ont été fixés avant tout calcul ([#19740](https://github.com/jsboige/CoursIA/issues/19740)). Le Sharpe est calculé à taux sans risque nul sur la valeur du portefeuille à chaque clôture, par une analyse hors dépôt ; il diffère donc du Sharpe affiché par QC, qui retranche un taux sans risque.

| Version | Sharpe | CAGR | Pire baisse | Rotation par an | Exposition brute moyenne |
|---------|--------|------|-------------|-----------------|--------------------------|
| `intent` (défaut) | 0,83 | 10,6 % | −24,4 % | 7,8 | 1,00 |
| `base` (code avant #19740) | 0,90 | 5,0 % | −11,5 % | 3,8 | 0,40 |
| SectorMomentum seul (`sm`) | 0,63 | 8,9 % | −24,9 % | 6,7 | 1,00 |
| RegimeSwitching seul (`rs`) | 0,90 | 12,5 % | −27,5 % | 9,5 | 1,00 |
| SPY détenu (`spy`) | 0,83 | 13,8 % | −33,7 % | 0,09 | 1,00 |
| 60 % SPY / 40 % IEF (`sixty40`) | 0,88 | 8,9 % | −21,1 % | 0,29 | 1,00 |

**Verdict.** Il est `NO BEATS` pour `base` comme pour `intent` : aucun écart de Sharpe avec les références n'est significatif. La différence est testée par bootstrap circulaire par blocs de 21 séances (10 000 tirages, correction de Holm sur les deux références).

| Candidate | Écart avec SPY [IC 95 %] | Écart avec le 60/40 [IC 95 %] | p Holm |
|-----------|--------------------------|-------------------------------|--------|
| `intent` | −0,00 [−0,47 ; +0,43] | −0,05 [−0,50 ; +0,37] | 1,00 |
| `base` | +0,08 [−0,29 ; +0,41] | +0,02 [−0,36 ; +0,38] | 0,72 |

Aucune des deux candidates n'est positive sur deux des trois sous-périodes (2015-2018, 2019-2022, 2023 → 2026-07). `base` ne devance les références que sur 2015-2018 ; `intent` seulement sur 2023-2026. La grille de paramètres et le run à frais doublés n'étaient prévus que pour une candidate significative : ils n'ont pas été lancés.

**Apport de chaque tranche.** Sous `intent`, l'écart de Sharpe avec SectorMomentum seul vaut +0,20 [−0,03 ; +0,43] ; avec RegimeSwitching seul, il vaut −0,08 [−0,46 ; +0,29]. Ces deux écarts sont descriptifs, hors correction de Holm. Additionner les tranches améliore SectorMomentum, pas RegimeSwitching. Sous `base`, le composite est RegimeSwitching dilué par du liquide, et un Sharpe calculé à taux sans risque nul ne voit pas cette dilution : d'où un Sharpe de 0,90 pour un CAGR de 5,0 %.

**Choix du défaut.** `intent` est la conception annoncée par le projet : le docstring de `MultiStrategyPCM` décrit l'addition des tranches. `base` laisse 60 % du capital en liquide et ignore SectorMomentum. Ni l'une ni l'autre ne bat les références : le changement de défaut rend le projet conforme à sa description, il ne crée pas d'avantage mesuré. Son Sharpe est même inférieur à celui de `base` (0,83 contre 0,90).

**Limites.**
- IEF a remplacé TLT en connaissant la période 2015-2026 (commentaire de `alpha_models.py`) : il n'y a pas de période hors échantillon. Ce biais favorisait la candidate, ce qui renforce le `NO BEATS`.
- Les backtests demandaient une fin au 2026-09-30. L'organisation QC utilisée retient les 90 derniers jours et a ramené la fin au 2026-07-09, sans erreur. Toutes les versions ont tourné dans la même organisation : les comparaisons portent sur les mêmes séances.
- Sous `intent`, la statistique `PCM calls with SM` reste à 0 par construction, car elle compte les insights reçus par `determine_target_percent`. L'addition se lit dans l'exposition brute (1,00) et dans les ordres sur GLD (203 contre 111 sous `base`).

### Livre de référence : tranche de minuit (#20264)

Mesure du 2026-10-11 sur les nœuds QC, fenêtre codée 2015-01-01 → 2025-12-31, avant et après le correctif de la tranche de minuit ([#20264](https://github.com/jsboige/CoursIA/issues/20264)). Le protocole a été pré-enregistré sur l'issue avant les runs (commentaire `c.6103552152`) ; la colonne « avant » est le code de `main` au commit `bb89b25ab5`, exécuté tel quel.

Les livres `spy` et `sixty40` se rééquilibrent à la première barre journalière du mois. En résolution journalière, Lean livre un avis de dividende seul, dans une tranche datée de minuit, sans barre de cotation : cette tranche consommait le rééquilibrage du mois. L'ordre partait alors à minuit et s'exécutait à l'ouverture du jour même ; les autres mois, il partait à la clôture de la première séance et s'exécutait à l'ouverture de la suivante. Le correctif ne consomme le mois que sur une tranche portant une barre d'un titre du livre : tous les mois suivent désormais le second calendrier. Les modes Framework ne passaient pas par ce test et n'ont pas changé ; le commit `e8a077acb0` (#20286) a ensuite étendu le même test aux deux alphas, dont la re-mesure #21349 mesure l'effet.

| | `spy` avant | `spy` après | `sixty40` avant | `sixty40` après |
|---|---|---|---|---|
| Ordres datés de minuit, heure de New York | 1, sur 1 mois | 0 | 192, sur 101 mois | 0 |
| Ordres | 2 | 2 | 213 | 220 |
| Sharpe (QC) | 0,538 | 0,538 | 0,461 | 0,465 |
| CAGR | 13,46 % | 13,46 % | 8,73 % | 8,77 % |
| Pire baisse | −33,7 % | −33,7 % | −21,1 % | −21,1 % |
| Frais, part du capital initial | 0,004 % | 0,004 % | 0,215 % | 0,222 % |
| Backtest | `1beca6af` | `47c3a129` | `f6e7540d` | `2936bdba` |

Le Sharpe affiché par QC bouge au plus de 0,004, sous le seuil de 0,05 fixé d'avance : les lignes `spy` et `sixty40` de la mesure ci-dessus, calculées avec le code d'avant, ne sont pas réécrites, et le verdict ne change pas.

#### Complément hors échantillon (arbitrage #20264 → #20310)

Mesure du 2026-10-11 sur la fenêtre OOS disjointe 2026-01-02 → 2026-07-13 (131 dates tradables), exigée par l'arbitrage de [#20264](https://github.com/jsboige/CoursIA/issues/20264) et pré-enregistrée avant les runs (commentaire `c.6109598714`). Mêmes projets cloud que la mesure ci-dessus, fenêtres passées par paramètres `start`/`end`, code inchangé. La fin demandée était le 2026-09-30 : les nœuds de calcul QC utilisés retiennent les 90 derniers jours et l'ont ramenée au 2026-07-13, sans erreur ; avant et après tournent sur les mêmes séances. Fenêtre courte (la fenêtre codée court jusqu'au 2025-12-31) : les premières semaines portent le warm-up du lookback momentum, à l'identique pour les deux variantes.

| | `spy` avant | `spy` après | `sixty40` avant | `sixty40` après |
|---|---|---|---|---|
| Ordres | 2 | 2 | 13 | 13 |
| Ordres de minuit | 1 | 0 | 11 | 0 |
| Sharpe (QC) | 0,860 | 0,861 | 0,482 | 0,483 |
| CAGR | 19,08 % | 19,09 % | 10,43 % | 10,45 % |
| Pire baisse | −8,8 % | −8,8 % | −5,9 % | −5,9 % |
| Backtest | `4b8005f1` | `f3ca6eb1` | `443bc016` | `196a80fd` |

Verdict `NO DEGRADATION` : écarts ≤ 0,001 partout. Les deux variantes passent le même nombre d'ordres ; l'« après » les passe tous à la clôture, l'« avant » en passait 12 sur 15 à minuit.

### Chiffres antérieurs à #19740

Le tableau ci-dessous date d'avant la mesure ; il est conservé pour l'historique (backtest 2015-01-01 → 2025-12-31).

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.185 |
| CAGR | 4.728 % |
| Net Profit | 66.272 % |
| Max Drawdown | 11.500 % |
| Total Orders | 520 |
| Win Rate | 73 % |
| Alpha | -0.008 |
| Beta | 0.218 |
| Sortino | 0.196 |

Le verdict d'alors était « Sous-performance » : RegimeSwitching aurait dilué les rendements dans le mélange 60/40, et l'étape suivante proposée était de tester T80/RS20 ou T90/RS10.

**Lecture corrigée par #19740.**
- **Tableau.** Le run `readme` (`base` sur la même période) le reproduit : Sharpe QC 0,21, CAGR 4,72 %, pire baisse 11,5 %, 522 ordres. Ces chiffres mesuraient RegimeSwitching à 40 % et 60 % de liquide, pas un mélange 60/40 : SectorMomentum n'a jamais tradé. Le beta faible (0,218) et le CAGR bas viennent du liquide. Changer les parts sous `base` ne change que la part de liquide : la piste T80/RS20 n'avait pas d'objet.
- **Statut « Edge » du registre.** Il citait un run hors échantillon 2023-2026 (projet 28871239) : Sharpe QC 0,145, PSR 73,52 %, 183 ordres. Le run `oos` (`base`, 2023-01-01 → 2026-05-01, 834 séances) ne le reproduit pas : Sharpe QC 0,133, PSR 2,5 %, 136 ordres. Hypothèse non vérifiée : ce projet a tourné sur une autre version du code. Le 73,52 % du registre est le PSR de ce petit échantillon, pas une mesure contre une référence.

## Paramètres

| Paramètre | Défaut | Description |
|-----------|--------|-------------|
| `mode` | `intent` | `intent` : tranches additionnées sur les ETF communs · `base` : code avant #19740 (RegimeSwitching à 40 %, reste en liquide) · `sm`, `rs` : une seule alpha, à 100 % · `spy`, `sixty40` : références détenues, rééquilibrées le premier jour de bourse du mois |
| `sm_allocation` | 0.60 | Tranche SectorMomentum (0.60 = 60 %) |
| `rs_allocation` | 0.40 | Tranche RegimeSwitching (0.40 = 40 %) |
| `sm_weights` | 0.4,0.2,0.2,0.2 | Poids des horizons 1, 3, 6 et 12 mois dans le score de SectorMomentum |
| `rs_lookback` | 63 | Horizon du momentum de RegimeSwitching, en séances |
| `start`, `end` | 2015-01-01, 2025-12-31 | Dates du backtest (`AAAA-MM-JJ`) |
| `brokerage` | `ibkr` | `none` : modèle de courtier par défaut de Lean, sans frais Interactive Brokers |
| `fee_mult` | 1 | Multiplicateur des frais du courtier (2 = frais doublés) |

Le graphique `shadow` porte la valeur du portefeuille à chaque clôture, les frais cumulés et la rotation cumulée (contrat du rejeu en ombre, #18923). Les statistiques d'exécution `Orders <ETF>` comptent les ordres exécutés par ETF ; `Gross exposure` est l'exposition brute moyenne ; `PCM calls`, `PCM calls with SM` et `SM UP reaching PCM` comptent les appels du modèle de construction et les insights de SectorMomentum qu'il reçoit.

## Cloud IDs

- Project ID : 31243821
- Organization : d600793ee4caecb03441a09fc2d00f7f
- Mesure #19740 : projet 37485593, dans une organisation éducative sponsorisée par QuantConnect
- Re-mesure #21349 : projets 38257493 (`main`), 38257551 (témoin), 38258154 et 38258197 (attribution), sur QC Cloud

## Période de backtest

Par défaut 2015-01-01 à 2025-12-31. La mesure #19740 et la re-mesure #21349 portent sur 2015-01-02 à 2026-07-09.

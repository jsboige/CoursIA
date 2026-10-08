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

- `main.py` : Configuration de l'algorithme avec CompositeAlpha et MultiStrategyPCM
- `alpha_models.py` : Classes SectorMomentumAlpha et RegimeSwitchingAlpha
- `portfolio_construction.py` : MultiStrategyPCM pour l'allocation de capital par stratégie
- `quantbook.ipynb` : QuantBook de recherche du composite Momentum + RegimeSwitching (données natives QC, pré-backtest)

## Performance

### Mesure #19740 : `NO BEATS`

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

## Période de backtest

Par défaut 2015-01-01 à 2025-12-31. La mesure #19740 porte sur 2015-01-02 à 2026-07-09.

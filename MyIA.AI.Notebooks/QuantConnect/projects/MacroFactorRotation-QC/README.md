# MacroFactorRotation-QC

**Classe d'actifs :** Multi-actifs (rotation macro et sizing d'exposition)
**Projets cloud QC :** `MacroFactorRotation-QC` (ID 32730301, original) ; `MacroFactorRotation-ASG-14722` (ID 36141780, experimentation alignee de l'issue #14722)

## Description

Consolidation experimentale (issue #14722) du projet de rotation macro : la
baseline DecisionTree est preservee a l'identique, et une variante de
controle ASG (Aggregate Sales Growth) ajoutee comme bras de comparaison sur
une fenetre alignee. Un seul fichier `main.py`, une seule classe
`MacroFactorRotationAlgorithm` pilotee par le parametre `mode`.

## Architecture

| Bras | Parametre | Mecanique |
|------|-----------|-----------|
| Baseline (defaut) | `mode=baseline` | Rotation macro multi-actifs SPY/GLD/BND/BTCUSD selon VIX, courbe 10Y-3M et fed funds, `DecisionTreeRegressor` reentraine mensuellement, 150 % d'exposition brute, BTC plafonne a 10 % (QC Strategy Library #72, logique d'origine inchangee) |
| ASG | `mode=asg` | Sizing d'exposition SPY/BIL de l'article QC research #21132 : ASG mensuelle (croissance annuelle du CA winsorisee 1/99, ponderee par capitalisation, univers USA primaires hors Financial Services / Real Estate), regression OLS a fenetre croissante du rendement excedentaire mensuel de SPY sur l'ASG retardée d'un mois, prevision `alpha + beta*ASG`, exposition `clip(forecast/(3*variance_120m), 0, 1.5)`, reliquat en BIL |

Parametres optionnels communs (alignement de l'experimentation) :
`start_date`, `end_date`, `trading_start` (format YYYYMMDD). Sans ces
parametres, le bras baseline reproduit le comportement d'origine.

Les fonctions pures du bras ASG (winsorisation, agregation cap-ponderee,
OLS retarde, variance 120 mois, bornes de poids) sont extraites dans
`asg_helpers.py` (aucune dependance LEAN) et couvertes par
`tests/test_asg_helpers.py` (9 tests pytest, executions locales vertes).

## Provenance

- **Baseline** : QC Strategy Library #72, "Monthly Macro Factor Cross-Asset
  Rotation" de Derek Melchin, clone 2026-04-05. Metriques annoncees par la
  bibliotheque : Sharpe OOS 1Y 1.23, CAGR 5Y 33.45 %, MaxDD 27.60 %.
- **Bras ASG** : QC research #21132, "Sizing Market Exposure With Aggregate
  Sales Growth" de Derek Melchin (juillet 2026). L'article rapporte Sharpe
  0.753 contre 0.412 pour SPY sur juillet 2021 - juillet 2026, sans modele
  explicite de frais/slippage, et qualifie lui-meme sa robustesse
  parametrique d'instable sur cet echantillon court (moyenne de grille
  0.670, fenetre 11 ans a 0.55). Source primaire : Garfinkel, Hribar &
  Hsiao (2025), "Aggregate Sales Growth and Stock Market Returns"
  (SSRN 5066654), archivee hors Git dans `G:\Mon Drive\MyIA\IA\Bibliographie IA\Trading\`.

## Experimentation alignee #14722

Fenetre, couts et capital strictement identiques pour les deux bras :

- **Fenetre fixe** : 2007-01-01 -> 2025-01-01 (capital 100 000 USD,
  benchmark SPY). Amendement audit pre-PR : la fenetre demarre en 2007
  pour fournir a la variance les 10 annees de l'article plus une marge
  avant le premier echange.
- **Entrainement/warmup** : 2007-01 -> 2017-12. Le bras ASG accumule ses
  series mensuelles - 131 valeurs d'ASG (2007-02 -> 2017-12) et 130
  rendements excedentaires (2007-03 -> 2017-12 ; le warm-up de 35 jours
  avale les evenements de janvier et fevrier 2007) - de sorte que la
  variance 120 mois de l'article est PLEINE des le premier echange de
  janvier 2018 (fenetre pleine + ~10 mois de marge). Le bras baseline
  n'echange pas : aucun des deux bras n'echange.
- **OOS** : 2018-01 -> 2025-01 (84 evenements mensuels ou les deux bras
  tradent). Les metriques pleine periode partagent le meme prefixe plat
  2007-2017 (100 % cash) : la comparaison directe reste valide.
- **Couts** : brokerage par defaut QC pour les deux bras (modeles de frais
  QC identiques, fills par defaut, aucun modele de slippage explicite -
  l'article #21132 n'en annonce pas non plus).
- **Garde-fou variance (amendement audit pre-PR)** : la premiere version
  de l'experimentation (v1, fenetre 2012-2025) tolerait une variance
  estimee sur seulement 60 mois (`MIN_VARIANCE_OBSERVATIONS = 60`), ce qui
  laissait le bras ASG echanger des 71 rendements - un relachement de la
  mecanique de l'article, corrige : la variance exige desormais la fenetre
  PLEINE de 120 mois (`MIN_VARIANCE_OBSERVATIONS = VARIANCE_WINDOW`), et
  les deux bras ont ete relances (v2) sur la fenetre 2007-2025. Les
  metriques v1 ci-dessous sont conservees uniquement pour tracabilite.
- **Bug latent corrige** : le clone local portait
  `set_brokerage_model(INTERACTIVE_BROKERS...)`, qui rejette les cibles
  Crypto ("Unsupported security type: Crypto", erreur runtime constatee au
  premier backtest v1). Le projet cloud d'origine (32730301) tourne sans
  brokerage model depuis le precedent "brokerage-fix-v2" (2026-06-10) ;
  la ligne est retiree pour les deux bras, conformement au commentaire
  d'origine de la strategie (multi-actifs : aucun broker reel unique).

## Metriques backtest v2 (QC Cloud, 2026-09-05)

Projet `MacroFactorRotation-ASG-14722` (ID 36141780), compile
`3f91dbe0544942bce2c7a47ea73cbb97-1748601bd97343c8210c636f8add2b34`
(code amendement 120 mois), une execution par bras, statut Completed
(progress 1), parametres `mode=baseline|asg`, `start_date=20070101`,
`end_date=20250101`, `trading_start=20180101`.

| Metrique | Bras baseline (53f10a127e160966176247f2018e68bc) | Bras ASG (149b8c44c0eaf887395e697e50da38e1) |
|----------|------------|-----------|
| Sharpe Ratio | 0.227 | 0.234 |
| CAGR | 5.750 % | 5.643 % |
| Max Drawdown | 41.900 % | 47.800 % |
| Profit net total | 173.809 % | 168.841 % |
| Ordres | 261 | 139 |
| PSR | 0.004 % | 0.005 % |

Controle de validite : le bras baseline v2 produit exactement les memes
trades que v1 (261 ordres, profit net 173.809 % identiques) - l'extension
2007-2012 ne fait qu'allonger le prefixe plat en cash, comme prevu.

Metriques v1 supersedees (fenetre 2012-2025, variance tolerait 60 mois ;
backtests 7877e240 / 5500f174, compile b9fc7f7c) : baseline Sharpe 0.325,
CAGR 8.047 %, MaxDD 41.900 % ; ASG Sharpe 0.404, CAGR 10.214 %, MaxDD
47.800 %. L'apparent avantage de Sharpe du bras ASG en v1 etait un artefact
du relachement de la fenetre de variance : avec la mecanique exacte de
l'article (variance 120 mois pleine), il disparait.

Reference : baseline deployee non contrainte (projet 32730301, backtest
`a99c2b6ad7c4a0ffe94bc70484170b56`, fenetre propre 10 ans) : Sharpe 0.731,
CAGR 22.626 %, MaxDD 42.000 % - chiffres non comparables aux bras alignes
(fenetre et prefixe plat differents), cites pour la tracabilite.

## Verdict : INCONCLUSIVE

Lecture descriptive : sur la fenetre alignee 2007-2025 avec la mecanique
exacte de l'article (variance 120 mois pleine), les deux bras sont
statistiquement indiscernables - Sharpe 0.234 vs 0.227, CAGR 5.6 % vs
5.8 % - et le bras ASG conserve un drawdown plus profond (47.8 % vs
41.9 %), coherent avec son exposition SPY pouvant atteindre 150 %. Aucune
amelioration statistiquement etablie n'est revendiquee : comparaison sur
une seule fenetre, PSR des deux bras tres loin de tout seuil de confiance
(0.004 % et 0.005 %), et pas de protocole multi-seed / Diebold-Mariano.
Les deux bras sont deterministes (pas de graine a varier), le protocole
BEATS strict ne s'applique donc pas ; le verdict honnete reste
INCONCLUSIVE. Le resultat v1 (Sharpe ASG 0.404 vs 0.325) illustre au
passage la sensibilite du sizing a la fenetre de variance - motivation
supplementaire pour ne pas revendiquer d'edge sur cet echantillon.

## How to Run

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/MacroFactorRotation-QC"`
**QC Cloud :** copier `main.py` + `asg_helpers.py` dans un projet Py, puis
lancer deux backtests avec les parametres `mode=baseline|asg`,
`start_date=20070101`, `end_date=20250101`, `trading_start=20180101`.
**Tests locaux :** `python -m pytest tests/test_asg_helpers.py` depuis le
dossier du projet.

## Files

- `main.py` - strategie deux bras (baseline preservee + variante ASG)
- `asg_helpers.py` - fonctions pures ASG (winsorisation, agregation, OLS, variance, bornes)
- `tests/test_asg_helpers.py` - tests pytest locaux (9 tests)

## References

- [QC research #21132 - Sizing Market Exposure With Aggregate Sales Growth](https://www.quantconnect.com/research/21132/sizing-market-exposure-with-aggregate-sales-growth/)
- Garfinkel, Hribar & Hsiao (2025), Aggregate Sales Growth and Stock Market Returns, SSRN 5066654
- [QC Strategy Library #72 - Monthly Macro Factor Cross-Asset Rotation](https://www.quantconnect.com/strategies/72)
- Issue #14722 (verdict CONSOLIDATION, label quantconnect-research)

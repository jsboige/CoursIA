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

- **Fenetre fixe** : 2012-01-01 -> 2025-01-01 (capital 100 000 USD, benchmark SPY).
- **Entrainement/warmup** : 2012-01 -> 2017-12. Le bras ASG accumule ses
  series mensuelles (72 mois d'ASG, 71 rendements excedentaires) ; le bras
  baseline n'echange pas. Aucun des deux bras n'echange.
- **OOS** : 2018-01 -> 2025-01 (84 evenements mensuels ou les deux bras
  tradent). Les metriques pleine periode partagent le meme prefixe plat
  2012-2017 (100 % cash) : la comparaison directe reste valide.
- **Couts** : brokerage par defaut QC pour les deux bras (modeles de frais
  QC identiques, fills par defaut, aucun modele de slippage explicite -
  l'article #21132 n'en annonce pas non plus).
- **Bug latent corrige** : le clone local portait
  `set_brokerage_model(INTERACTIVE_BROKERS...)`, qui rejette les cibles
  Crypto ("Unsupported security type: Crypto", erreur runtime constatee au
  premier backtest v1). Le projet cloud d'origine (32730301) tourne sans
  brokerage model depuis le precedent "brokerage-fix-v2" (2026-06-10) ;
  la ligne est retiree pour les deux bras, conformement au commentaire
  d'origine de la strategie (multi-actifs : aucun broker reel unique).

## Metriques backtest (QC Cloud, 2026-09-05)

Projet `MacroFactorRotation-ASG-14722` (ID 36141780), compile
`b9fc7f7c5a6e18d802c921396df1de6e`, une execution par bras, statut
Completed (progress 1).

| Metrique | Bras baseline (7877e24091314e0b65ffe7a3f8b4d1da) | Bras ASG (5500f1749e4f16776759ab7433558a0d) |
|----------|------------|-----------|
| Sharpe Ratio | 0.325 | 0.404 |
| CAGR | 8.047 % | 10.214 % |
| Max Drawdown | 41.900 % | 47.800 % |
| Profit net total | 173.809 % | 254.446 % |
| Ordres | 261 | 150 |
| PSR | 0.157 % | 0.413 % |

Reference : baseline deployee non contrainte (projet 32730301, backtest
`a99c2b6ad7c4a0ffe94bc70484170b56`, fenetre propre 10 ans) : Sharpe 0.731,
CAGR 22.626 %, MaxDD 42.000 % - chiffres non comparables aux bras alignes
(fenetre et prefixe plat differents), cites pour la tracabilite.

## Verdict : INCONCLUSIVE

Lecture descriptive : sur la meme fenetre alignee, le bras ASG affiche un
Sharpe (0.404 vs 0.325) et un CAGR (10.2 % vs 8.0 %) superieurs, mais un
drawdown plus profond (47.8 % vs 41.9 %), coherent avec son exposition SPY
pouvant atteindre 150 %. Aucune amelioration statistiquement etablie n'est
revendiquee : comparaison sur une seule fenetre, PSR des deux bras tres
loin de tout seuil de confiance (0.16 % et 0.41 %), et pas de protocole
multi-seed / Diebold-Mariano. Les deux bras sont deterministes (pas de
graine a varier), le protocole BEATS strict ne s'applique donc pas ; le
verdict honnete reste INCONCLUSIVE, avec un cout en drawdown a documenter
pour toute suite donnee au sizing ASG.

## How to Run

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/MacroFactorRotation-QC"`
**QC Cloud :** copier `main.py` + `asg_helpers.py` dans un projet Py, puis
lancer deux backtests avec les parametres `mode=baseline|asg`,
`start_date=20120101`, `end_date=20250101`, `trading_start=20180101`.
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

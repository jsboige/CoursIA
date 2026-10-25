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
| Reference SPY | `mode=spy` | SPY detenu a 100 % (#21329) |
| Reference 60/40 | `mode=6040` | SPY 60 %, BND 40 %, reequilibre au debut de chaque mois a la minute de la baseline (#21329) |

Tous les modes tracent la valeur du portefeuille a l'ouverture de chaque
seance de SPY dans le graphique `shadow` (series e0..e4, contrat #18923),
a partir de `trading_start`. C'est la serie que lit
`Paradox46Benchmarks/significance.py`. La baseline rend aussi une sonde
FRED en statistiques d'execution : `FRED same-day` (reequilibrages dont la
derniere ligne de facteurs porte la date du jour de decision), `FRED
2018-02` / `2020-03` / `2020-04` (date, VIXCLS lue, derniere etiquette) et
`Max gross target`. Ni la trace ni la sonde ne touchent aux decisions.

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
  series mensuelles : au premier echange de janvier 2018, au moins 130
  valeurs d'ASG et au moins 129 rendements excedentaires sont disponibles
  (bornes conservatives, valables meme si le warm-up de 35 jours ignorait
  les evenements de janvier et fevrier 2007) - la variance 120 mois de
  l'article est donc PLEINE des le premier echange, avec de la marge. Le
  bras baseline n'echange pas : aucun des deux bras n'echange.
- **OOS** : 2018-01 -> 2025-01 (84 evenements mensuels ou les deux bras
  tradent). Les metriques pleine periode partagent le meme prefixe plat
  2007-2017 (100 % cash) : la comparaison directe reste valide.
- **Couts** : brokerage par defaut QC pour les deux bras (modeles de frais
  QC identiques, fills par defaut, aucun modele de slippage explicite -
  l'article #21132 n'en annonce pas non plus).
- **Garde-fou variance (amendement audit pre-PR)** : la premiere version
  de l'experimentation (v1, fenetre 2012-2025) tolerait une variance
  estimee sur seulement 60 mois (`MIN_VARIANCE_OBSERVATIONS = 60`), ce qui
  laissait le bras ASG echanger avant que la fenetre pleine ne soit
  remplie - un relachement de la mecanique de l'article, corrige : la
  variance exige desormais la fenetre PLEINE de 120 mois
  (`MIN_VARIANCE_OBSERVATIONS = VARIANCE_WINDOW`), et les deux bras ont
  ete relances (v2) sur la fenetre 2007-2025.

  Les metriques v1 ci-dessous
  sont conservees uniquement pour tracabilite.
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

## Metriques v3 : references detenues (QC Cloud, 2026-10-18, #21329)

Protocole et predictions ecrits dans #21329 avant le premier backtest. Projet
de mesure 38062065, compilation
`738d6530208bae8cb5639986ebff79ad-b5d0fa28b193d474c67379fa8d9a6ca3`, memes
parametres de fenetre que v2.

| Metrique (QC, fenetre 2007-2025, prefixe plat compris) | baseline | ASG | SPY detenu | 60/40 detenu |
|----------|----------|-----|------------|--------------|
| Backtest | `f8a43f4a3ce3508c95c80282516b45a4` | `341ed473a48a774f2626c9603dbd01df` | `3320c0ec4afbcef9cee073efe082e8b8` | `94fb834664452cf895ba3f9b6f535978` |
| Sharpe Ratio | 0.228 | 0.288 | 0.210 | 0.092 |
| CAGR | 5.734 % | 5.596 % | 5.092 % | 3.320 % |
| Max Drawdown | 41.900 % | 18.500 % | 33.600 % | 21.900 % |
| Profit net total | 173.075 % | 166.654 % | 144.643 % | 80.082 % |
| Ordres | 261 | 133 | 1 | 142 |

Significativite : `Paradox46Benchmarks/significance.py` sur la trace `shadow`
(1761 seances, du 2018-01-02 au 2024-12-31), taux sans risque nul, correction
de Holm sur les six p-valeurs de chaque bras.

| Comparaison | Sharpe du bras | Sharpe de la reference | Ecart | p Ledoit-Wolf | p bootstrap (unilaterale) | p de Holm (Ledoit-Wolf) |
|-------------|------|------|------|------|------|------|
| baseline vs SPY detenu | 0.734 | 0.761 | -0.026 | 0.906 | 0.557 | 1.000 |
| baseline vs 60/40 | 0.734 | 0.758 | -0.024 | 0.914 | 0.548 | 1.000 |
| ASG vs SPY detenu | 1.015 | 0.761 | +0.254 | 0.441 | 0.198 | 1.000 |
| ASG vs 60/40 | 1.015 | 0.758 | +0.256 | 0.478 | 0.211 | 1.000 |

Les intervalles de confiance a 95 % du bootstrap contiennent zero dans les
quatre cas (ASG contre SPY : -0.34 a +0.84).

**Sonde FRED : pas de lecture du futur.** Aux trois dates de controle, la
derniere ligne de facteurs porte la cloture de la veille :

| Decision | VIXCLS lu | Cloture de la veille | Cloture du jour |
|----------|-----------|----------------------|-----------------|
| 2018-02-01 | 13.54 | 13.54 (31/01) | 13.47 |
| 2020-03-02 | 40.11 | 40.11 (28/02) | 33.42 |
| 2020-04-01 | 53.54 | 53.54 (31/03) | 57.06 |

L'index des lignes FRED est l'heure de fin de barre, soit le lendemain de
l'observation : la ligne du 31/01 est datee du 01/02. Le compteur
`FRED same-day` (44/84) compte donc ces dates de fin de barre, pas des
lectures du jour. Il ne mesure pas une fuite, et la baseline n'est pas
corrigee. `Max gross target` vaut 1.600, l'exposition brute cible prevue.

**Derive depuis v2.** Les memes bras ne rendent plus les chiffres de v2 :
ASG 139 ordres devenus 133, drawdown 47.8 % devenu 18.5 %, profit net
168.841 % devenu 166.654 % ; baseline 261 ordres inchanges, profit net
173.809 % devenu 173.075 %. Le code de `main` (sans les ajouts de #21329),
recompile dans un projet temoin (38062287), rend exactement les chiffres
v3 (ASG `ab2fa09d16619cc96ab7f5b0187ab793`, baseline
`8193647b349d5663d27a58a6acffa55d`) : les ajouts ne changent aucune
decision, la derive vient des donnees ou du moteur QC entre le 2026-09-05
et le 2026-10-18.

**Cause etablie par #21333 (journaux d'ordres + sonde 38066227).** Par bras :

- **baseline : ajustement des prix.** Les 261 ordres tombent aux memes
  minutes sur les memes symboles ; le rapport de prix v3/v2 est constant
  par symbole (SPY 0.9975, BND 0.9965, BIL 0.9971, GLD et BTCUSD 1.0000) -
  la signature du mode `Adjusted` apres de nouvelles distributions. Une
  seule decision change sur 79 mois (novembre 2022), cause probable non
  verifiee : une distribution ajoutee deplace une etiquette
  `TOTAL_RETURN` de l'arbre.
- **ASG : donnees fondamentales.** La decision change des le premier
  echange (exposition 1.29 -> 1.02) et differe sur 76 mois sur 80. La
  sonde isole un defaut de notre code - la capitalisation Morningstar est
  vide avant mi-2009 (4.9 % de couverture en 2007), l'ASG 2007-2009 est
  ponderee sur 94 a 178 titres - defaut corrige depuis par #21336 (section
  v4), mais qui N'EST PAS la cause de la derive : le bras avec repli ne
  ramene pas v2. Le champ fondamental exact qui a bouge entre septembre
  et octobre (valeurs de `revenue_growth`, composition de l'univers,
  capitalisations servies) n'est pas isole, et la serie v2 n'est pas
  reconstructible : v2 n'avait trace ni l'ASG ni la couverture.

**Regle de protocole qui en decoule : relancer le temoin avant de
comparer deux mesures eloignees dans le temps.** Une mesure QC Cloud est
un couple (code, donnees du jour) ; comparer un bras fraichement mesure a
une reference mesuree des semaines plus tot compare aussi deux etats des
donnees. Chaque campagne de mesure re-excute donc les quatre bras le meme
jour, meme quand un seul a change.

## Verdict v3 : baseline NO BEATS, ASG INCONCLUSIVE

Regle ecrite dans #21329 : `BEATS` si l'ecart de Sharpe est positif et la
p de Holm (Ledoit-Wolf) inferieure a 0.05 contre les deux references ;
`NO BEATS` si le Sharpe ponctuel est inferieur a celui de SPY detenu ;
`INCONCLUSIVE` sinon.

- **baseline : NO BEATS.** Sharpe 0.734 contre 0.761 pour SPY detenu, avec
  une exposition brute cible de 1.6. La prediction etait `INCONCLUSIVE` :
  elle est manquee, de peu (ecart -0.026, tres loin de toute
  significativite dans un sens comme dans l'autre).
- **ASG : INCONCLUSIVE**, comme predit. Sharpe 1.015 contre 0.761 : le bras
  rend en moyenne autant que SPY (ecart de moyennes, p 0.93) avec moins de
  volatilite, mais l'ecart de Sharpe n'est significatif contre aucune des
  deux references (p de Holm 1.000).

Le verdict v2 (`INCONCLUSIVE`, bras compares entre eux seulement) est
remplace par celui-ci. Il decrivait les deux bras comme statistiquement
indiscernables sans l'avoir teste, et un drawdown ASG de 47.8 % que la
mesure actuelle ne reproduit pas.

## Metriques v4 : capitalisation reconstruite (QC Cloud, 2026-10-19, #21336)

Correctif #21336 : repli de capitalisation `price * split_factor *
shares_outstanding` quand `market_cap` n'est pas strictement positive
(`asg_helpers.effective_market_cap`, branche dans `_select_assets` sans
parametre), et garde de couverture `Cap coverage (min)` (statistique
d'execution, statuee dans `on_end_of_algorithm`). Les quatre bras sont
relances le meme jour (regle de protocole ci-dessus). Projet de mesure
38062065, compilation
`923704de16caf422f17c52c2d52a10a2-1158cb83922599abf473ad0182149513`.

| Metrique (QC, fenetre 2007-2025, prefixe plat compris) | baseline | ASG | SPY detenu | 60/40 detenu |
|----------|----------|-----|------------|--------------|
| Backtest | `72a73b70ef0b3d3c61ec9abd36344865` | `f6212f7d87d80231609be63b7f43169c` | `d593f2c46532b7070dbbed342e703985` | `95d9a8ae84a573b6a527dbfd5f0d68be` |
| Sharpe Ratio | 0.228 | 0.288 | 0.210 | 0.092 |
| CAGR | 5.734 % | 5.406 % | 5.092 % | 3.320 % |
| Max Drawdown | 41.900 % | 18.200 % | 33.600 % | 21.900 % |
| Profit net total | 173.075 % | 158.182 % | 144.643 % | 80.082 % |
| Ordres | 261 | 120 | 1 | 142 |

Les trois bras non concernes par le correctif (baseline, SPY detenu,
60/40) rendent exactement les chiffres v3 : le correctif ne touche que
la coupe fondamentale du bras ASG. Le bras ASG rend exactement la
contre-epreuve `cap_fallback=1` de #21333 (120 ordres, 158.182 %,
drawdown 18.2 %) : le repli inconditionnel reproduit la sonde
parametree. Garde de couverture : `Cap coverage (min)` = **94.4 %** sur
la fenetre - le minimum tombe en 2007, ou certains titres n'ont ni
capitalisation directe ni facteurs de repli exploitables - contre
4.9 % de couverture sans correctif (sonde #21333).

Significativite : `Paradox46Benchmarks/significance.py` sur la trace
`shadow` (1761 seances, du 2018-01-02 au 2024-12-31), taux sans risque
nul, correction de Holm sur les six p-valeurs de chaque bras.

| Comparaison | Sharpe du bras | Sharpe de la reference | Ecart | p Ledoit-Wolf | p bootstrap (unilaterale) | p de Holm (Ledoit-Wolf) |
|-------------|------|------|------|------|------|------|
| baseline vs SPY detenu | 0.734 | 0.761 | -0.026 | 0.906 | 0.557 | 1.000 |
| baseline vs 60/40 | 0.734 | 0.758 | -0.024 | 0.914 | 0.548 | 1.000 |
| ASG vs SPY detenu | 1.053 | 0.761 | +0.293 | 0.408 | 0.183 | 1.000 |
| ASG vs 60/40 | 1.053 | 0.758 | +0.295 | 0.440 | 0.197 | 1.000 |

Les intervalles de confiance a 95 % du bootstrap contiennent zero dans
les quatre cas (ASG contre SPY : -0.33 a +0.93).

## Verdict v4 : baseline NO BEATS, ASG INCONCLUSIVE

Meme regle que v3 (#21329). Le verdict ne change pas de camp ; l'estime
ponctuelle du bras ASG se renforce : Sharpe ombre 1.015 -> 1.053, ecart
a SPY detenu +0.254 -> +0.293, toujours loin de toute significativite
(p de Holm 1.000). Le bras rend en moyenne autant que SPY detenu (ecart
de moyennes journalieres -0.6 bp, p 0.977) avec moins de volatilite.

Le verdict v3 reste l'histoire de la mesure du 2026-10-18 (capitalisation
non reconstruite) ; le verdict courant est celui-ci.

## How to Run

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/MacroFactorRotation-QC"`
**QC Cloud :** copier `main.py` + `asg_helpers.py` dans un projet Py, puis
lancer quatre backtests avec les parametres `mode=baseline|asg|spy|6040`,
`start_date=20070101`, `end_date=20250101`, `trading_start=20180101`.
**Significativite :** telecharger le graphique `shadow` de chaque backtest,
puis, depuis `Paradox46Benchmarks/` :
`python significance.py --strategy baseline.json --bench spy=spy.json --bench 6040=6040.json`
(idem avec `asg.json`).
**Tests locaux :** `python -m pytest tests/test_asg_helpers.py` depuis le
dossier du projet.

## Files

- `main.py` - strategie deux bras (baseline preservee + variante ASG), deux references detenues (SPY, 60/40), trace `shadow`, sonde FRED et garde de couverture de capitalisation (#21336)
- `asg_helpers.py` - fonctions pures ASG (winsorisation, agregation, capitalisation effective avec repli, OLS, variance, bornes)
- `tests/test_asg_helpers.py` - tests pytest locaux (13 tests)

## References

- [QC research #21132 - Sizing Market Exposure With Aggregate Sales Growth](https://www.quantconnect.com/research/21132/sizing-market-exposure-with-aggregate-sales-growth/)
- Garfinkel, Hribar & Hsiao (2025), Aggregate Sales Growth and Stock Market Returns, SSRN 5066654
- [QC Strategy Library #72 - Monthly Macro Factor Cross-Asset Rotation](https://www.quantconnect.com/strategies/72)
- Issue #14722 (verdict CONSOLIDATION, label quantconnect-research)

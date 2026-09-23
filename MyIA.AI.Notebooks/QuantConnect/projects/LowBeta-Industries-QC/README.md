# LowBeta-Industries-QC

Banc de mesure de l'anomalie bas-bêta à partir de l'article de recherche QuantConnect **« Low Beta Portfolios Across Industries »** (Derek Melchin, [research 18469](https://www.quantconnect.com/research/18469/low-beta-portfolios-across-industries/), publié le 2024-12-23). Issue #17500, EPIC #11698 (moisson qc-research).

L'article annonce qu'un portefeuille bas-bêta équipondéré par industrie bat SPY (Sharpe 0,669 contre 0,624). Ce projet vérifie cette affirmation, et la confronte à la construction de la source que l'article cite : trois bras sur le **même** harnais QC Cloud, avec les mêmes données, la même fenêtre (2010-01-02 → 2026-08-31), le même capital et les mêmes frais.

| Bras (`arm`) | Construction |
|---|---|
| `article` | port fidèle du code de l'article : long-only, \|bêta\| OLS sur 60 jours, médiane **globale**, poids de rang, industries équipondérées |
| `bab` | *industry-neutral BAB* d'Asness, Frazzini et Pedersen (2014) : bêta de Frazzini-Pedersen, médiane **par industrie**, jambe basse levée à bêta 1 et jambe haute réduite à bêta 1, industries équipondérées |
| `spy` | buy-and-hold SPY (la référence de l'article) |

## Ce que l'article fait, et ce que sa source fait

L'article cite Asness, Frazzini et Pedersen, *Low-Risk Investing without Industry Bets* (FAJ 70(4), 2014 ; noté AFP ci-dessous). Son code s'en écarte sur tous les points qui font de l'AFP une mesure de l'anomalie :

| | Article QC | AFP 2014 (*industry-neutral BAB*) |
|---|---|---|
| Positions | long-only | long bas-bêta **et** short haut-bêta |
| Exposition au marché | bêta réalisé 0,79 (article) | bêta ex ante **0** : chaque jambe est ramenée à bêta 1 |
| Médiane de séparation | **globale** (tout l'univers) | **par industrie** |
| Estimateur du bêta | OLS sur 60 jours, en valeur absolue | σ_i/σ_m sur un an de rendements quotidiens × corrélation sur cinq ans de rendements à trois jours, contracté vers 1 : β = 0,6·β_ts + 0,4 (p. 27) |
| Levier | 1 | $Long 1,34 / $Short 0,77 en moyenne (Table 3, p. 33) |
| Résultat publié | Sharpe 0,669 contre 0,624 (2010 → 2024) | Sharpe 0,85 (US 1926-2012, industries équipondérées), excès 0,65 %/mois, t = 7,76 (Table 3, p. 33) |

Deux conséquences, avant tout backtest :

1. Comparer les Sharpe d'un portefeuille de bêta 0,79 et d'un portefeuille de bêta 1 ne dit rien de l'anomalie. La question juste est celle d'un **alpha CAPM** : le bras `article` gagne-t-il plus que ce que son bêta lui donne ?
2. Les paramètres de l'article (60 jours, 50 actions par industrie) ont été choisis sur une grille de 30 combinaisons évaluée sur la **même** période que le résultat publié (« 19 sur 30 battent le benchmark »). Ce Sharpe est in-sample. La fenêtre 2025-01 → 2026-07, postérieure à la publication, est la seule vraiment hors échantillon pour lui.

## Le bras `bab` : ce qui vient du papier, ce qui ne peut pas en venir

Aucun paramètre du bras `bab` n'a été réglé sur les résultats. Chacun a une source :

| Paramètre | Valeur | Source |
|---|---|---|
| fenêtre de volatilité | 252 jours | AFP p. 27 (un an de rendements quotidiens) |
| fenêtre de corrélation | 1260 jours de rendements à 3 jours | AFP p. 27 (cinq ans, rendements à trois jours contre la non-synchronicité) |
| historique minimal | 120 jours (volatilité), 750 jours (corrélation) | Frazzini-Pedersen, JFE 2014, section 3.1 |
| contraction | β = 0,6·β_ts + 0,4 | AFP p. 27, Frazzini-Pedersen 2014 (Vasicek) |
| poids | rang du bêta centré, k = 2/Σ\|z − z̄\| | Frazzini-Pedersen 2014, éq. 16 |
| rééquilibrage | mensuel | AFP p. 28 |
| industries | équipondérées | AFP Table 3, colonne « Equal Weighted » |

Trois écarts sont imposés par la plateforme, pas choisis :

- **Univers** : les 50 actions les plus liquides de chaque *industry group* Morningstar (celui de l'article), pas tout CRSP. C'est un univers de grandes capitalisations : le point de comparaison de l'AFP est donc son Panel B, « Largest 1,000 stocks » (Table 6, p. 39 : excès brut 0,32 %/mois, t = 4,77, Sharpe brut 0,52, net de coûts 0,43).
- **Industries** : les *industry groups* Morningstar, pas les 49 industries de Fama-French. Une industrie qui a moins de 4 bêtas valides est ignorée (garde-fou mécanique : avec 3 noms, une jambe tient sur une seule action).
- **Trésorerie** : LEAN ne verse aucun intérêt sur le cash et ne facture pas l'emprunt de titres. Le rendement en excès se reconstruit hors plateforme (voir *Méthode*).

`bab_scale` (0,5 par défaut) fixe la taille du portefeuille : chaque jambe vaut `bab_scale` × 1/β de sa jambe. Le Sharpe et le t de Student n'en dépendent pas ; le rendement « par dollar de BAB » s'obtient en divisant par `bab_scale`.

## Méthode

`main.py` trace chaque mois, dans les trois bras, le rendement du compte, celui de SPY, et l'exposition nette et brute moyennes du mois (graphique `Monthly`). `analyze_arms.py` fait le reste hors plateforme :

- **rendement en excès** : R − exposition nette × r_f, avec r_f = bon du Trésor à 3 mois (FRED `TB3MS`). C'est la définition de l'AFP, corrigée de ce que LEAN ne rémunère pas le cash ;
- **alpha CAPM** du bras `article` contre SPY, écarts-types de Newey-West ;
- **différence de Sharpe** `article` − `spy` : erreur-type HAC de Ledoit et Wolf (2008, section 3.1). Le test usuel de Jobson-Korkie-Memmel suppose des rendements normaux et indépendants ; celui-ci tient sous queues épaisses et autocorrélation, au prix d'être un peu libéral en petit échantillon ;
- **BAB par dollar** : moyenne, t de Newey-West, volatilité, bêta réalisé ;
- **sous-périodes** fixées par les sources, pas par les résultats : 2010-2012 (recouvre la fin de l'échantillon de l'AFP), 2013 → 2026 (hors échantillon de l'AFP), 2010-2024 (in-sample de l'article), 2025 → 2026 (hors échantillon de l'article), plus cinq tranches temporelles égales.

```bash
# 1. backtests (QC Cloud, projet 36854709) : un par bras, paramètre "arm"
# 2. lecture des graphiques et des statistiques (identifiants QC par variables d'environnement)
export QC_API_USER_ID=... QC_API_ACCESS_TOKEN=...
python analyze_arms.py fetch --project 36854709 --backtest article=<id> --backtest bab=<id> --backtest spy=<id>
# 3. tests (sans accès QC)
python analyze_arms.py stats
```

Les paramètres d'un backtest partent en JSON (`{"parameters": {"arm": "bab"}}`) : le champ de formulaire `parameters[arm]` est ignoré sans erreur, et le bras par défaut (`article`) tourne à la place.

`fetch` lit les graphiques avec `count=5000` : sous ce seuil, `/backtests/chart/read` ré-échantillonne la série sur une grille uniforme en interpolant, et les valeurs lues ne sont plus celles tracées. `fetch` refuse donc toute série dont un point tombe après le 5 du mois ou dont deux points tombent le même mois.

## Résultats

Trois backtests QC Cloud (projet 36854709), lancés le 2026-09-23 : du 2010-01-02 au 2026-08-31, 10 M$ initiaux, frais du modèle de courtage par défaut de LEAN. Les tableaux sont produits par `python analyze_arms.py markdown` à partir de `measures/`, sans retouche. Les tests portent sur 199 mois, de janvier 2010 à juillet 2026 : août 2026, que la fin du backtest interrompt, n'est pas clos par un point mensuel.

### Statistiques de la plateforme

| Statistique QC | `article` | `bab` | `spy` |
|---|---|---|---|
| Sharpe Ratio | 0.623 | -0.455 | 0.615 |
| Probabilistic Sharpe Ratio | 2.386% | 0.000% | 1.986% |
| Compounding Annual Return | 13.007% | -0.214% | 14.126% |
| Drawdown | 36.000% | 16.200% | 33.700% |
| Annual Standard Deviation | 0.124 | 0.044 | 0.142 |
| Alpha | 0.01 | -0.018 | -0.001 |
| Beta | 0.758 | -0.027 | 0.998 |
| Total Fees | $1923415.26 | $246422.80 | $591.40 |
| Total Orders | 153285 | 94168 | 1 |
| Portfolio Turnover | 2.16% | 0.72% | 0.02% |
| Net Profit | 668.105% | -3.505% | 805.298% |
| End Equity | 76810459.40 | 9649544.69 | 90529781.62 |
| backtest | `c2f7f72af7bbb7f032a4cf1c96394c39` | `adc09dac2d31396c085b034b15ac03c8` | `4aaf269a4ce08fe4020cf3551320a5f4` |

Le port reproduit l'en-tête de l'article : Sharpe 0,623 contre 0,615 pour SPY (l'article : 0,669 contre 0,624 sur 2010-2024), bêta 0,76 (l'article : 0,79). Le portefeuille bas-bêta ne réduit pourtant pas la perte maximale : 36,0 % contre 33,7 % pour SPY.

Le bras `bab` perd 3,5 % en seize ans et demi (Sharpe −0,455), pour un bêta quotidien de −0,03 : il est bien neutre au marché, et il ne rapporte rien. Ses 94 168 ordres coûtent 246 423 $ de frais, soit environ 0,025 %/mois par dollar de BAB : les frais n'expliquent pas l'absence de prime. LEAN ne facture pas l'emprunt de titres, si bien qu'un vrai short aurait coûté davantage.

### Deux conventions de Sharpe, deux classements

QC calcule son Sharpe sur les rendements quotidiens, contre sa propre série de taux sans risque, pour un compte dont le cash ne rapporte rien. `analyze_arms.py` le calcule sur les rendements mensuels en excès (R − exposition nette × TB3MS). Les niveaux diffèrent, et surtout **le classement s'inverse** : `article` passe devant SPY avec la convention de QC (0,623 contre 0,615), derrière avec la convention en excès (0,82 contre 0,89). Un écart dont le signe dépend de la convention de mesure n'est pas un résultat. Le test de Ledoit-Wolf le confirme ci-dessous.

### Tests par fenêtre

| Fenêtre | mois | Sharpe excès article / bab / spy | Δ Sharpe article − spy (z, p) | alpha article %/mois (t) | bêta article | BAB %/mois par $ (t) | vol. BAB | bêta BAB |
|---|---|---|---|---|---|---|---|---|
| 2010-01 → 2026-07 (tout) | 199 | 0,82 / −0,08 / 0,89 | −0,07 (−0,54, 0,587) | 0,042 (0,27) | 0,88 | −0,069 (−0,36) | 10,5 % | −0,10 |
| 2010-01 → 2012-12 (fin de l'échantillon AFP) | 36 | 0,95 / −0,22 / 0,70 | 0,25 (1,17, 0,242) | 0,283 (1,23) | 0,94 | −0,222 (−0,36) | 12,2 % | −0,06 |
| 2013-01 → 2026-07 (hors échantillon AFP) | 163 | 0,78 / −0,04 / 0,93 | −0,14 (−0,97, 0,334) | −0,008 (−0,04) | 0,87 | −0,036 (−0,18) | 10,2 % | −0,11 |
| 2010-01 → 2024-12 (in-sample de l'article) | 180 | 0,85 / −0,08 / 0,87 | −0,02 (−0,16, 0,873) | 0,079 (0,47) | 0,92 | −0,067 (−0,33) | 10,4 % | −0,07 |
| 2025-01 → 2026-07 (hors échantillon de l'article) | 19 | 0,37 / −0,09 / 1,02 | −0,66 (−1,06, 0,290) | −0,174 (−0,40) | 0,40 | −0,090 (−0,10) | 12,0 % | −0,46 |

- **Bras `article`.** Son alpha CAPM est indiscernable de zéro dans toutes les fenêtres : 0,042 %/mois (t = 0,27) sur 2010-2026, −0,008 %/mois (t = −0,04) après 2013. Son bêta mensuel réalisé vaut 0,88 : le portefeuille est le marché, avec un bêta un peu plus faible. La différence de Sharpe avec SPY vaut −0,07 (z = −0,54, p = 0,59), avec une erreur-type d'environ 0,13 sur seize ans. L'écart publié par l'article (0,669 − 0,624 = 0,045) représente 0,35 erreur-type : aucun test ne peut le distinguer de zéro. Même sur la période in-sample de l'article (2010-2024), la différence est nulle (−0,02, p = 0,87).
- **Après la publication** (2025-01 → 2026-07, 19 mois), `article` fait nettement moins bien que SPY : Sharpe 0,37 contre 1,02, alpha −0,174 %/mois (t = −0,40), bêta tombé à 0,40. Sur 19 mois, l'erreur-type de la différence de Sharpe est d'environ 0,62 : cette fenêtre ne tranche rien.
- **Bras `bab`.** Son rendement en excès par dollar vaut −0,069 %/mois (t = −0,36) sur 2010-2026 et −0,036 %/mois (t = −0,18) hors échantillon de l'AFP. Son bêta réalisé est légèrement négatif (−0,11, t = −1,87 sur 2013-2026). Corrigé de ce bêta, l'alpha CAPM passe à +0,083 %/mois (t = 0,46) : toujours indiscernable de zéro.

### Confrontation aux chiffres de l'AFP

Les chiffres de l'AFP portent sur les États-Unis, colonne *Equal Weighted* de l'*industry-neutral BAB*. Ses alphas sont des alphas à **quatre facteurs** (notes de la Table 5), que ce banc n'estime pas : la mesure mise en regard est la plus proche disponible ici, pas la même.

| Mesure de l'AFP | AFP | Mesure la plus proche ici | Écart, en erreurs-types de notre estimation |
|---|---|---|---|
| 1926-2012, *Largest 1,000 stocks*, rendement brut (Table 6, panel B, p. 39) | 0,32 %/mois (t = 4,77) | 2013-2026, rendement en excès : −0,036 %/mois (t = −0,18) | 1,8 |
| 1926-2012, *Large cap*, alpha à quatre facteurs (Table 5, panel B, p. 38) | 0,23 %/mois (t = 3,87) | 2013-2026, alpha CAPM : +0,083 %/mois (t = 0,46) | 0,8 |
| 2010-2012, alpha à quatre facteurs (Table 5, panel A, p. 38) | 0,67 %/mois (t = 2,94) | 2010-2012, alpha CAPM : −0,168 %/mois (t = −0,24) | 1,2 |
| $Long / $Short moyens (Table 3, p. 33) | 1,34 / 0,77 | 1,16 / 0,75 | — |

| Composition du BAB (moyenne sur les rééquilibrages) | valeur |
|---|---|
| rééquilibrages | 201 |
| industries retenues | 54,8 |
| noms en portefeuille | 1657 |
| bêta ex ante, jambe basse / jambe haute | 0,87 / 1,36 |
| $Long / $Short par dollar de BAB | 1,16 / 0,75 |

Le BAB tient en moyenne 54,8 industries et 1 657 noms. Sa jambe basse a un bêta ex ante de 0,87, contre environ 0,75 chez l'AFP (1/1,34) ; le levier qui porte la prime y est donc plus faible (1,16 contre 1,34). Une hypothèse est compatible avec cet écart sans que ce banc la teste : dans un univers de grandes capitalisations, la moitié basse des bêtas reste plus proche du marché.

**Puissance du banc.** Avec une volatilité de 10,2 %/an sur 163 mois, l'erreur-type du BAB hors échantillon vaut 0,20 %/mois. À deux erreurs-types, ce banc ne détecte qu'une prime d'au moins 0,39 %/mois. Les primes de l'AFP sur les grandes capitalisations (0,32 %/mois brut, 0,23 %/mois d'alpha) sont en dessous de ce seuil. L'absence de prime mesurée ici n'est donc **pas une réfutation** de l'AFP : c'est l'absence, sur 2013-2026 et dans cet univers, d'une prime assez grande pour être vue.

### Tranches temporelles

| Tranche | alpha article %/mois | bêta article | BAB %/mois par $ (t) |
|---|---|---|---|
| 2010-01 → 2013-04 | 0,303 | 0,95 | −0,059 (−0,11) |
| 2013-05 → 2016-08 | 0,034 | 0,90 | 0,190 (0,66) |
| 2016-09 → 2019-12 | −0,162 | 0,91 | 0,193 (1,04) |
| 2020-01 → 2023-04 | 0,546 | 0,94 | −0,426 (−0,72) |
| 2023-05 → 2026-07 | −0,374 | 0,63 | −0,250 (−0,54) |

L'alpha du bras `article` change de signe d'une tranche à l'autre (de −0,374 à +0,546 %/mois). Le BAB est positif sur 2013-2019 (t ≤ 1,04) et négatif ailleurs. Aucune tranche ne porte de résultat significatif.

### Verdicts

| Question | Verdict | Preuve |
|---|---|---|
| Le bras `article` bat-il SPY, corrigé du risque ? | **NO BEATS** | alpha CAPM 0,042 %/mois (t = 0,27) ; Δ Sharpe −0,07 (p = 0,59) sur 199 mois |
| Le bras `article` bat-il SPY après sa publication ? | **INCONCLUSIVE** | 0,37 contre 1,02 sur 19 mois, erreur-type ≈ 0,62 |
| L'*industry-neutral BAB* gagne-t-il une prime hors de l'échantillon de l'AFP ? | **NO BEATS** | −0,036 %/mois (t = −0,18) sur 163 mois ; alpha CAPM +0,083 %/mois (t = 0,46) |
| Ce banc réfute-t-il l'AFP ? | **INCONCLUSIVE** | primes de l'AFP à 0,8 et 1,8 erreur-type, sous le seuil de détection |

Limites :

- **un backtest par bras** : le backtest est déterministe, l'incertitude est d'échantillonnage (celle des tests ci-dessus) et aucune graine n'intervient ;
- **univers** : les 50 actions les plus liquides de chaque *industry group* Morningstar, soit l'univers de l'article et non tout CRSP ;
- **financement** : LEAN ne verse pas d'intérêt sur le cash et ne facture pas l'emprunt de titres. Le premier défaut est corrigé hors plateforme, le second ne l'est pas, ce qui rend le BAB plutôt optimiste.

## Références

- Asness, C., Frazzini, A., Pedersen, L. H. (2014). *Low-Risk Investing without Industry Bets*. Financial Analysts Journal 70(4), 24-41. `G:\Mon Drive\MyIA\IA\Bibliographie IA\Trading\2014 - Asness Frazzini Pedersen - Low-Risk Investing without Industry Bets.pdf`
- Frazzini, A., Pedersen, L. H. (2014). *Betting Against Beta*. Journal of Financial Economics 111(1), 1-25 (version du 2013-05-10). `G:\Mon Drive\MyIA\IA\Bibliographie IA\Trading\2014 - Frazzini Pedersen - Betting Against Beta (JFE 111(1), version 2013-05-10).pdf`
- Frazzini, A., Pedersen, L. H. (2010). *Betting Against Beta*. NBER Working Paper 16601. `G:\Mon Drive\MyIA\IA\Bibliographie IA\Trading\2010 - Frazzini Pedersen - Betting Against Beta (NBER w16601).pdf`
- Ledoit, O., Wolf, M. (2008). *Robust Performance Hypothesis Testing with the Sharpe Ratio*. Journal of Empirical Finance 15(5) ; version IEW Working Paper 320 (janvier 2008). `G:\Mon Drive\MyIA\IA\Bibliographie IA\Trading\2008 - Ledoit Wolf - Robust Performance Hypothesis Testing with the Sharpe Ratio (IEW WP 320).pdf`
- Melchin, D. (2024). *Low Beta Portfolios Across Industries*. QuantConnect Research 18469.

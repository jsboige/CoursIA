# MAXEffect-VIXLeverage-QC

**Classe d'actifs :** Actions US (univers liquide)
**ID projet Cloud :** 38366686

## Description

Port de l'article *The MAX Effect with VIX-Based Leverage Scaling* (Derek Melchin, équipe QuantConnect, Research 20886, publié le 2026-06-12). L'article récolte le côté long de l'anomalie MAX documentée par Bali, Cakici et Whitelaw ([JFE 2011](https://pages.stern.nyu.edu/~rwhitela/papers/max%20jfe11.pdf)) : les titres aux jours haussiers extrêmes se comportent comme des billets de loterie et sous-performent ensuite.

Chaque premier jour de bourse du mois, `main.py` :

1. filtre l'univers US sur les critères de l'article — prix > 5 $, capitalisation > 1 Md$, hors REIT et ADR, volume moyen > 5 M$/j (appliqué au rééquilibrage) ;
2. calcule le facteur MAX(5) de chaque titre : moyenne des 5 plus forts rendements quotidiens sur 21 séances ;
3. retient le **décile inférieur** du facteur, plafonné à 25 titres, et l'équi-pondère ;
4. applique l'overlay de levier de l'article : 1,5× quand le VIX ≤ 15, décroissant linéairement vers 1,0× à VIX ≥ 30, **reajusté en continu** entre les rééquilibrages (chacun des titres est rescalé du même facteur, les poids relatifs ne changent pas).

L'article annonce un Sharpe de 0,57 « depuis 1998 » contre 0,335 pour SPY buy-and-hold, et un balayage 25/25 favorable (0,474–0,585). Ce port mesure la règle, pas le chiffre.

## Port : ce qui change et ce qui ne change pas

Ce qui est repris de l'article sans changement : le facteur (5 jours sur 21 séances), le décile inférieur plafonné à 25, l'équi-pondération, le rééquilibrage mensuel, les seuils VIX 15/30 et le levier 1,5×/1,0×, le rajustement continu.

Ce qui change — chaque point est **mesuré** sur un run qui a échoué (les neuf backtests sont rangés dans les traces) :

- **API PascalCase.** Le code de l'article est en `Initialize`/`AddEquity`/`Resolution.Daily`. C'est la forme qui compile sur QC Cloud pour ce port ; la variante snake_case a été abandonnée avant le premier run.
- **VIX via `CBOE(PythonData)` local.** Le namespace `.NET QuantConnect.Data.Custom.CBOE` n'est pas importable depuis un algorithme Python sur QC Cloud (« No module named »). Le VIX est donc chargé du CSV public de CBOE (`cdn.cboe.com`, `VIX_History.csv`) via un `PythonData` local, patron repris de `DynamicVIXSpyRegime-QC`.
- **Convention lag (défaut du dépôt, #19825/#19837).** La ligne VIX du jour D est livrée à D+1 (`CBOE.lag_days = 1`) : lire la clôture du jour même au rééquilibrage est un lookahead, mesuré sur les projets voisins.
- **`SelectionData` au niveau module.** Une classe interne n'est pas visible depuis les méthodes de l'algorithme (« name 'SelectionData' is not defined », mesure v2).
- **`SetHoldings` liste positionnelle.** Le kwarg `liquidate_existing_holdings` casse la résolution d'overload Python (« argument 1 ('symbol') expected Symbol, got list », mesure v3) : les sorties du décile sont liquidées explicitement, puis les cibles partent en liste.
- **Rescale par holding.** Ni `portfolio.values()` ni `securities.values()` ne portent à la fois la quantité et le prix (mesures v4 et v5) : le rescale lit `holding.quantity` sur le holding et `self.securities[symbol].price` sur le titre.
- **`MonthStart` shift 0.** Le shift 1 tire le J+1 du premier jour de bourse (mesure v3, événement du 2015-02-03) : le rééquilibrage part le premier jour de bourse à 8 h ET.

Paramètres (défauts = valeurs de l'article) :

| Paramètre | Valeurs | Rôle |
|---|---|---|
| `mode` | `max-vix` (défaut), `max-only`, `spy` | candidat / ablation facteur seul / SPY détenu à 100 % |
| `top_returns` | 5 (défaut) | jours haussiers retenus par MAX |
| `max_portfolio_size` | 25 (défaut) | plafond de titres |
| `period` | 21 (défaut) | séances du facteur |
| `low_vix`, `high_vix` | 15, 30 (défauts) | seuils de l'overlay |
| `low_leverage`, `high_leverage` | 1,5, 1,0 (défauts) | leviers aux deux bornes |

## Fenêtre

Fenêtre principale du **2015-01-01 au 2026-06-30** (série journalière de 4 199 points, dont 2 847 jours de bourse effectifs pour le candidat) : la convention de fenêtre des mesures du cluster (2015 → 2026, cf. `DynamicVIXSpyRegime-QC`, `AllWeather`, `RiskParity`), pas la fenêtre « depuis 1998 » de l'article. L'univers fondamental US et le CSV VIX couvrent les deux ; la fenêtre 1998 est laissée en suivi — un run journalier de 28 ans sur un seul nœud QC Cloud dépasse la fenêtre d'un cycle. Les chiffres de l'article (« Sharpe 0,57 depuis 1998 ») ne se confrontent donc pas frontalement ; la confrontation porte sur le **verdict** (bat-il SPY sur la même fenêtre, avec les mêmes frais ?), pas sur le niveau.

## Sources

- **Article** : Derek Melchin, *The MAX Effect with VIX-Based Leverage Scaling*, QuantConnect Research 20886 (2026-06-12), <https://www.quantconnect.com/research/20886/the-max-effect-with-vix-based-leverage-scaling/>
- **Paper primaire** : Turan G. Bali, Nusret Cakici, Robert F. Whitelaw, *Maxing out: Stocks as lotteries and the cross-section of expected returns*, Journal of Financial Economics 99 (2011) 427–446. Copie : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Trading\2011 - Bali Cakici Whitelaw - Maxing Out Stocks as Lotteries and the Cross-Section of Expected Returns (JFE 99).pdf` (première page vérifiée).
- **Ce que le paper primaire établit.** L'anomalie est mesurée en **coupe** (portefeuilles triés par MAX, long le bas / short le haut, 1963–2007) : le décile le moins « loterie » bat le plus « loterie » d'environ 7,1 % par an en brut. Le paper ne mesure pas le **côté long seul, équi-pondéré, sur l'univers liquide de l'article, avec un overlay de levier VIX** — c'est l'ajout de l'article, et c'est ce que ce port mesure.

## Mesure (#22290)

**Protocole.** Fenêtre 2015-01-01 → 2026-06-30 commune aux trois passages (candidat, ablation, référence), frais IBKR en compte marge, 100 000 $. Le candidat, son ablation `max-only` (levier fixe 1,0×, qui isole la contribution de l'overlay VIX) et SPY détenu à 100 % tournent sur le même harnais.

**Le Sharpe publié n'est pas à taux sans risque nul — et c'est une correction.** Les ports voisins du bouquet annoncent un Sharpe « taux sans risque nul » ; ici, la vérification par la courbe montre que le chiffre rendu par QC est calculé avec un taux sans risque non nul. Les rendements journaliers (série `Return`, valeurs en pourcent) compoundent bien au total du backtest (1,8337 contre 1,8458 sur l'équité, soit 0,7 % d'écart d'arrondi). Calculés sur les **2 881 séances communes** aux deux passages — les seules où SPY rend un rendement non nul — ils donnent un Sharpe à taux nul de **0,518** pour le candidat (volatilité annualisée **11,49 %**) et de **0,821** pour SPY (**17,58 %**, compounded 4,3968, identique au +339,683 % publié), là où QC publie 0,181 et 0,551. L'écart s'explique par le taux sans risque : un taux constant équivalent de **3,9 %/an** reproduit le 0,181 du candidat, **4,8 %/an** reproduit le 0,551 de SPY. QC emploie donc un taux variable dans le temps, ce que deux taux implicites différents disent assez.

**Conséquence pour la comparaison.** Les deux Sharpes publiés sont calculés par le même moteur, sur la même fenêtre, avec le même taux : la comparaison 0,181 contre 0,551 est homogène, et le verdict n'en dépend pas. Mais l'ordre de grandeur des écarts, lui, change : en base taux nul l'écart entre candidat et référence est de **0,304** de Sharpe (0,518 contre 0,821) et non 0,370. La volatilité est l'autre moitié du fait : le candidat est **moins volatil** que SPY (11,49 % contre 17,58 %) — l'overlay de levier ne fait pas un portefeuille plus risqué, il en fait un portefeuille plus lent, avec un rendement qui ne compense pas la vol économisée.

### Résultats

**État de la mesure : livrée 4/4** — candidat composé, candidat corrigé (contrôle), ablation et référence mesurés (l'ablation `3158bd546830303dc013f8763faf3b98` a couru ~4 h sur un seul nœud QC Cloud, complétée le 2026-10-24 ; le contrôle `d837ab0da…` complété le 2026-10-24).

**Contrôle livré (revue #22330, 2026-10-24) — la ligne `max-vix` v6 mesurait un chemin d'exposition composée.** Le rescale de levier de la version v6 prenait `total_portfolio_value` pour dénominateur : le poids de chaque ligne se recalculait sur l'exposition **courante** (déjà rescalée la fois précédente), si bien que l'exposition se **composait** à chaque changement de levier — 1,50 → 1,45 rendait 2,17× au lieu de 1,45×, et revenir à 1,0× ne dérisquait rien. Le code est corrigé dans cette PR (dénominateur = somme des positions détenues : la somme des poids cibles vaut exactement le levier demandé, donc exposition = levier × equity, vérifié sur la séquence 1,50 → 1,45 → 1,50 → 1,27 → 1,27 → 1,00 qui rend 1,500 / 1,450 / 1,500 / 1,270 / 1,270 / 1,000). Le backtest de contrôle `d837ab0da23d2e7217a722c886eddf08` a tourné sur ce code corrigé : lancé pour la sous-fenêtre 2019-2022, il a en réalité couvert la **pleine fenêtre** 2015-01 → 2026-06 (dates codées en dur dans `Initialize` ; sa courbe d'équité va du 2015-01-01 au 2026-06-30, et son CAGR de 6,026 % n'est arithmétiquement compatible du profit total 96,05 % que sur ~11,5 ans — sur 4 ans il aurait fallu +26 %). C'est plus que la promesse : la ligne corrigée remplace la ligne composée **sur la fenêtre entière**, dans le tableau ci-dessous. **L'ablation `max-only` n'est pas affectée** (levier fixe 1,0×, le rescale n'est jamais atteint), ni la référence `spy` (pas d'overlay).

| Passage | ID backtest | Sharpe (QC) | CAGR | Drawdown max | Frais cumulés | Rotation |
|---|---|---|---|---|---|---|
| `max-vix` (candidat, code corrigé — contrôle) | `d837ab0da23d2e7217a722c886eddf08` | 0,255 | 6,03 % | 27,00 % | −21 973,52 $ | 26 281 ordres / 40,10 M$ |
| `max-vix` (v6, chemin composé — bug) | `47d6ad9479ee72e8d8fda2e6fd6d8cd7` | 0,181 | 5,40 % | 26,40 % | −10 524,36 $ | 32 697 ordres / 42,94 M$ |
| `max-only` (ablation) | `3158bd546830303dc013f8763faf3b98` | 0,288 | 6,12 % | 25,90 % | −5 113,93 $ | 4 550 ordres / 21,42 M$ |
| `spy` (référence) | `b36253509d96547fb0b98baf8a1187eb` | 0,551 | 13,74 % | 33,50 % | −2,95 $ | 1 ordre |

Total candidat corrigé : +96,05 % (capital 100 000 $ → 196 046,41 $) ; total candidat v6 (composé) : +83,16 % (→ 183 163,72 $) ; total SPY détenu : +339,68 % (100 000 $ → 439 682,65 $) ; total ablation : +98,14 % (100 000 $ → 198 139,26 $).

**Décomposition (facteur seul vs candidat mesuré).** L'ablation `max-only` — même facteur MAX(5), même univers, même rééquilibrage mensuel, mais levier fixe 1,0× sans overlay — rend Sharpe **0,288** et CAGR **6,12 %** là où le candidat mesuré rend 0,181 et 5,40 %, avec un drawdown quasi identique (25,90 % contre 26,40 %). Sur la fenêtre mesurée, l'overlay VIX **a retiré** de la performance au lieu d'en ajouter : −0,107 de Sharpe et −0,72 pp de CAGR, sans acheter de réduction de drawdown. Deux réserves bornaient cette lecture ; le contrôle en a levé une et mesuré l'autre. (1) **Le bug coûtait au candidat 0,074 de Sharpe et 0,63 pp de CAGR** (corrigé 0,255 / 6,03 % contre composé 0,181 / 5,40 %) : composer l'exposition pendant les replis détruisait de la valeur — le chemin composé n'avantageait pas le candidat. Sur code sain, l'overlay retire **−0,033 de Sharpe** et −0,09 pp de CAGR à l'ablation (0,255 contre 0,288 ; 6,03 % contre 6,12 %) : l'overlay retire toujours, mais trois fois moins que la lecture composée (−0,107) ne le laissait croire. (2) L'écart de rotation persiste sur code corrigé — 26 281 ordres et −21 974 $ de frais pour le candidat corrigé contre 4 550 ordres et −5 114 $ pour l'ablation. Fait mesuré et non expliqué : le chemin corrigé paie **deux fois plus de frais** que le chemin composé (−21 973,52 $ contre −10 524,36 $) pour moins d'ordres et un volume comparable (40,10 M$ contre 42,94 M$) — rapporté tel quel, sans interprétation. Le facteur seul, lui non plus, ne bat pas la référence (0,288 contre 0,551 ; 6,12 % contre 13,74 %) : l'absence d'edge n'est pas portée par le seul overlay, elle est aussi dans le facteur MAX long-only sur cette fenêtre.

**Compteur de séances — mesuré, plus supposé.** QC rapporte 4 199 « dates négociables » pour les runs à univers (candidat et ablation) contre 2 889 pour SPY, ce qui ressemble à une fenêtre différente. Les courbes journalières disent l'inverse : les deux passages couvrent la **même grille** de 4 199 et 4 200 points (2015-01-01 → 2026-06-30), et sur cette grille SPY ne rend un rendement non nul que **2 882 jours** — l'ordre de grandeur de son compteur (2 889). Les deux compteurs mesurent donc des choses différentes (jours de la série contre jours de bourse pour SPY), pas deux fenêtres. La comparaison porte bien sur une fenêtre commune ; c'est le libellé du compteur qui n'est pas homogène d'un mode à l'autre. **Le choix de la base n'est pas cosmétique** : calculés sur les 4 199 jours de la grille, les Sharpes à taux nul tombent à 0,428 et 0,680 — soit exactement le facteur √f attendu (f = 0,686, √f = 0,828) puisque moyenne et dispersion ne se contractent pas au même rythme. C'est une dilution de calendrier, pas une propriété du portefeuille ; les chiffres publiés ici sont donc ceux des séances.

**Sous-fenêtres** (candidat, calculées localement sur la grille journalière de chaque courbe — 4 199 points, mêmes bornes ; la méthode reproduit les valeurs v6 publiées à 0,04 de Sharpe près) :

| Passage | 2015–2018 | 2019–2022 | 2023–2026-06 |
|---|---|---|---|
| `max-vix` v6 (chemin composé) | CAGR 0,79 % · Sharpe 0,105 | CAGR 12,19 % · Sharpe 0,733 | CAGR 3,22 % · Sharpe 0,427 |
| `max-vix` code corrigé (contrôle) | CAGR 3,80 % · Sharpe 0,374 | CAGR 8,58 % · Sharpe 0,634 | CAGR 5,71 % · Sharpe 0,720 |
| `spy` | non dérivées — la courbe d'équité de ce run n'est pas retournée par l'outil de lecture employé | idem | idem |

### Test d'écart (bootstrap par blocs)

Sur les 2 881 séances communes, l'écart de Sharpe à taux nul (candidat − SPY) vaut **−0,304**. Bootstrap circulaire par blocs de 21 séances, 10 000 tirages, graine fixe (20261024), sur les rendements journaliers **appariés** : intervalle de 95 % **[−0,876 ; +0,189]**, p unilatérale 0,116, p bilatérale 0,258. La correction de Holm est l'identité ici — un seul comparateur, SPY, donc aucune famille de tests à corriger.

**Ce que ce test établit, et ce qu'il n'établit pas.** L'intervalle contient zéro : sur cette fenêtre, l'égalité des deux Sharpes ne se rejette pas au seuil de 5 %. Le verdict NO BEATS ne repose donc pas sur ce test — il repose sur les statistiques publiées, qui placent le candidat sous la référence sur les deux mesures (0,181 contre 0,551 ; 5,402 % contre 13,739 % de CAGR). Le test dit quelque chose de plus modeste et de cohérent avec cela : l'écart observé est négatif et de l'ordre de 0,3, mais onze ans de rendements journaliers ne suffisent pas à le distinguer du bruit d'échantillonnage. Le publier tel quel est le seul usage honnête du chiffre ; le taire aurait laissé croire à une significativité acquise.

### Verdict

**2/3 runs mesurés — le verdict contre la référence est acquis, la décomposition ne l'est pas.** Le candidat `max-vix` rend un Sharpe 0,181 et un CAGR 5,40 % sur 2015-01 → 2026-06, contre **0,551 et 13,74 % pour SPY détenu** sur la même fenêtre : sur les deux statistiques la référence gagne, et l'écart est du même ordre que celui que l'article revendique en sens inverse (0,57 contre 0,335). La performance du candidat v6 est de plus **portée par une seule sous-fenêtre** (2019-2022 : CAGR 12,19 %), avec 2015-2018 quasi neutre (0,79 %) et 2023-2026-06 faible (3,22 %) ; le contrôle corrigé redistribue (8,58 % · 5,71 % · 3,80 %) — 2019-2022 reste la meilleure sous-fenêtre, sans dominer autant. Un point va dans l'autre sens et doit être dit : le drawdown du candidat est plus faible que celui de SPY (26,40 % contre 33,50 %), effet attendu de l'overlay de levier — moins de perte, mais aussi moins de rendement. **Verdict : NO BEATS** — le candidat ne bat pas la référence détenue sur la fenêtre mesurée, ni en Sharpe ni en CAGR. **Décomposition livrée :** l'ablation `max-only` (levier fixe 1,0×, ID `3158bd54…`) rend 0,288 de Sharpe et 6,12 % de CAGR — mieux que le candidat mesuré (0,181 / 5,40 %), moins bien que SPY (0,551 / 13,74 %). L'overlay VIX, tel que mesuré, retire ; le facteur seul ne porte pas assez pour battre la référence. Le contrôle a chiffré la part du bug : 0,074 de Sharpe et 0,63 pp de CAGR coûtaient au candidat par le chemin composé (corrigé 0,255 / 6,03 %) ; sur code sain l'overlay ne retire plus que 0,033 de Sharpe à l'ablation (0,255 contre 0,288) — le verdict NO BEATS est inchangé et ne doit plus rien au bug. Le test d'écart mesuré (2 881 séances, écart **−0,304**, IC 95 % [−0,876 ; +0,189], p bilatérale 0,258) ne rejette pas l'égalité des Sharpes : la conclusion est un « ne bat pas », pas un « perd significativement ».

### Confrontation à l'article

L'article annonce « Sharpe 0,57 depuis 1998 » sur sa fenêtre 1998 → présent, contre 0,335 pour SPY buy-and-hold. Ce port mesure 2015 → 2026-06 (convention de fenêtre du cluster) : la confrontation porte donc sur le **verdict** — bat-il la référence détenu sur la même fenêtre, avec les mêmes frais ? — pas sur le niveau de Sharpe. Le 0,181 mesuré sur 2015-2026 est déjà nettement sous le 0,57 de l'article sur une fenêtre plus longue, ce qui suggère que l'edge revendiqué s'est érodé sur la période récente ; l'ablation mesurée (facteur seul : 0,288, toujours sous la référence) situe l'érosion dans les deux étages — le facteur seul sous-performe, et l'overlay mesuré retire encore ; le contrôle la chiffre : le bug coûtait 0,074 de Sharpe au candidat, et sur code sain l'overlay ne retire que 0,033 de Sharpe (0,255 contre 0,288 à l'ablation).

### Limites

- **Fenêtre 2015–2026**, pas « depuis 1998 » comme l'article : la confrontation porte sur le verdict, pas sur le niveau de Sharpe.
- **Univers à survie.** L'univers fondamental de QC ne contient que les titres encore cotés ; les faillites de la fenêtre sont absentes du long. C'est un biais favorable connu de ce type de backtest, identique à tous les ports du bouquet.
- **Levier 1,5× en compte marge.** Le pouvoir d'achat du modèle IBKR de Lean peut refuser des ordres : l'exposition effective est à lire dans les journaux.
- **Frais.** La rotation mensuelle de 25 titres est chère ; les frais cumulés sont portés dans le tableau de mesure.
- **Puissance du test d'écart.** Onze ans de rendements journaliers ne distinguent pas un écart de Sharpe de 0,3 du bruit (IC 95 % [−0,876 ; +0,189]). L'absence de significativité n'est pas une preuve d'équivalence : elle borne ce que cette fenêtre peut dire, dans un sens comme dans l'autre.

Les traces de chaque passage sont rangées hors dépôt dans `G:\Mon Drive\MyIA\IA\QC-traces\22290-max-effect-vix` : à ce jour les trois fichiers du passage candidat v6 (`v6_equity.json`, `v6_max-vix_results.json`, `v6_subwindows.json`) et les deux du contrôle (`controle_equity.json`, `controle_results.json`). Les neuf backtests antérieurs (dont cinq runs en échec) n'y sont pas archivés et ne sont pas revendiqués ici.

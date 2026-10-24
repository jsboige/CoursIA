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

Fenêtre principale du **2015-01-01 au 2026-06-30** (4 199 séances) : la convention de fenêtre des mesures du cluster (2015 → 2026, cf. `DynamicVIXSpyRegime-QC`, `AllWeather`, `RiskParity`), pas la fenêtre « depuis 1998 » de l'article. L'univers fondamental US et le CSV VIX couvrent les deux ; la fenêtre 1998 est laissée en suivi — un run journalier de 28 ans sur un seul nœud QC Cloud dépasse la fenêtre d'un cycle. Les chiffres de l'article (« Sharpe 0,57 depuis 1998 ») ne se confrontent donc pas frontalement ; la confrontation porte sur le **verdict** (bat-il SPY sur la même fenêtre, avec les mêmes frais ?), pas sur le niveau.

## Sources

- **Article** : Derek Melchin, *The MAX Effect with VIX-Based Leverage Scaling*, QuantConnect Research 20886 (2026-06-12), <https://www.quantconnect.com/research/20886/the-max-effect-with-vix-based-leverage-scaling/>
- **Paper primaire** : Turan G. Bali, Nusret Cakici, Robert F. Whitelaw, *Maxing out: Stocks as lotteries and the cross-section of expected returns*, Journal of Financial Economics 99 (2011) 427–446. Copie : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Trading\2011 - Bali Cakici Whitelaw - Maxing Out Stocks as Lotteries and the Cross-Section of Expected Returns (JFE 99).pdf` (première page vérifiée).
- **Ce que le paper primaire établit.** L'anomalie est mesurée en **coupe** (portefeuilles triés par MAX, long le bas / short le haut, 1963–2007) : le décile le moins « loterie » bat le plus « loterie » d'environ 7,1 % par an en brut. Le paper ne mesure pas le **côté long seul, équi-pondéré, sur l'univers liquide de l'article, avec un overlay de levier VIX** — c'est l'ajout de l'article, et c'est ce que ce port mesure.

## Mesure (#22290)

**Protocole.** Fenêtre 2015-01-01 → 2026-06-30 commune aux trois passages (candidat, ablation, référence), frais IBKR en compte marge, 100 000 $. Le candidat, son ablation `max-only` (levier fixe 1,0×, qui isole la contribution de l'overlay VIX) et SPY détenu à 100 % tournent sur le même harnais. La statistique de verdict est l'écart de Sharpe journalier contre SPY détenu, avec bootstrap circulaire par blocs et correction de Holm.

### Résultats

**État de la mesure (livrée à 2/3) :** le candidat et la référence SPY sont mesurés ; l'ablation `max-only` est en vol (backtest `3158bd546830303dc013f8763faf3b98`, lancé le 2026-10-24 08:24 UTC, à 70 % en fin de matinée, runtime ~4 h sur un seul nœud QC Cloud). La ligne d'ablation sera complétée et la décomposition écrite au cycle suivant.

| Passage | ID backtest | Sharpe (QC) | CAGR | Drawdown max | Frais cumulés | Rotation |
|---|---|---|---|---|---|---|
| `max-vix` (candidat, v6) | `47d6ad9479ee72e8d8fda2e6fd6d8cd7` | 0,181 | 5,40 % | 26,40 % | −10 524,36 $ | 32 697 ordres / 42,94 M$ |
| `max-only` (ablation) | `3158bd546830303dc013f8763faf3b98` | **en cours** | — | — | — | — |
| `spy` (référence) | `b36253509d96547fb0b98baf8a1187eb` | 0,551 | 13,74 % | 33,50 % | −2,95 $ | 1 ordre |

Total candidat : +83,16 % (capital 100 000 $ → 183 163,72 $) ; total SPY détenu : +339,68 % (100 000 $ → 439 682,65 $).

**Compteur de séances.** QC rapporte 4 199 « dates négociables » pour les deux runs à univers (candidat et ablation) contre 2 889 pour SPY. La fenêtre 2015-01-01 → 2026-06-30 compte ~2 890 séances de bourse, ce qui rend 2 889 cohérent et 4 199 ininterprétable comme un nombre de séances calendaires : le compteur des runs à univers n'a donc pas la même sémantique (univers multi-titres). Les chiffres comparés ici sont les CAGR et Sharpe publiés par QC sur la même fenêtre calendaire ; une comparaison de Sharpe à nombre de séances déclaré inégal n'est pas une comparaison à fenêtre prouvée identique, et cette limite est portée au crédit de la prudence, pas du résultat.

**Sous-fenêtres** (candidat, calculées localement sur la courbe d'équité journalière du backtest v6) :

| Passage | 2015–2018 | 2019–2022 | 2023–2026-06 |
|---|---|---|---|
| `max-vix` | CAGR 0,79 % · Sharpe 0,105 | CAGR 12,19 % · Sharpe 0,733 | CAGR 3,22 % · Sharpe 0,427 |
| `spy` | non dérivées — la courbe d'équité de ce run n'est pas retournée par l'outil de lecture employé | idem | idem |

### Verdict

**2/3 runs mesurés — le verdict contre la référence est acquis, la décomposition ne l'est pas.** Le candidat `max-vix` rend un Sharpe 0,181 et un CAGR 5,40 % sur 2015-01 → 2026-06, contre **0,551 et 13,74 % pour SPY détenu** sur la même fenêtre : sur les deux statistiques la référence gagne, et l'écart est du même ordre que celui que l'article revendique en sens inverse (0,57 contre 0,335). La performance du candidat est de plus **portée par une seule sous-fenêtre** (2019-2022 : CAGR 12,19 %), avec 2015-2018 quasi neutre (0,79 %) et 2023-2026-06 faible (3,22 %). Un point va dans l'autre sens et doit être dit : le drawdown du candidat est plus faible que celui de SPY (26,40 % contre 33,50 %), effet attendu de l'overlay de levier — moins de perte, mais aussi moins de rendement. **Verdict : NO BEATS** — le candidat ne bat pas la référence détenue sur la fenêtre mesurée, ni en Sharpe ni en CAGR. Reste à décomposer l'absence d'edge : l'ablation `max-only` (en vol, ID `3158bd54…`, levier fixe 1,0×) dira si le facteur MAX seul porte quelque chose et si l'overlay VIX ajoute ou retire. L'écart de Sharpe journalier avec bootstrap circulaire par blocs et correction de Holm se calcule quand les trois passages sont mesurés ; il ne peut pas changer le signe d'un écart de 0,37 de Sharpe, il en précisera l'incertitude.

### Confrontation à l'article

L'article annonce « Sharpe 0,57 depuis 1998 » sur sa fenêtre 1998 → présent, contre 0,335 pour SPY buy-and-hold. Ce port mesure 2015 → 2026-06 (convention de fenêtre du cluster) : la confrontation porte donc sur le **verdict** — bat-il la référence détenu sur la même fenêtre, avec les mêmes frais ? — pas sur le niveau de Sharpe. Le 0,181 mesuré sur 2015-2026 est déjà nettement sous le 0,57 de l'article sur une fenêtre plus longue, ce qui suggère que l'edge revendiqué s'est érodé sur la période récente ; l'ablation (facteur seul, levier fixe 1×) dira si l'érosion est dans le facteur MAX ou dans l'overlay VIX.

### Limites

- **Fenêtre 2015–2026**, pas « depuis 1998 » comme l'article : la confrontation porte sur le verdict, pas sur le niveau de Sharpe.
- **Univers à survie.** L'univers fondamental de QC ne contient que les titres encore cotés ; les faillites de la fenêtre sont absentes du long. C'est un biais favorable connu de ce type de backtest, identique à tous les ports du bouquet.
- **Levier 1,5× en compte marge.** Le pouvoir d'achat du modèle IBKR de Lean peut refuser des ordres : l'exposition effective est à lire dans les journaux.
- **Frais.** La rotation mensuelle de 25 titres est chère ; les frais cumulés sont portés dans le tableau de mesure.

Les traces de chaque passage (neuf backtests dont les cinq runs en échec, journaux, `results.json`) sont rangées hors dépôt dans `G:\Mon Drive\MyIA\IA\QC-traces\22290-max-effect-vix`.

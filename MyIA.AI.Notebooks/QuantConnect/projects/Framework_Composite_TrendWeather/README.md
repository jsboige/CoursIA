# Framework_Composite_TrendWeather

**Classe d'actifs :** Actions US (ETF + actions)
**Cloud project ID :** 38458884 (espace de backtest du cours, mesures du 2026-11-09)

> 🇬🇧 **English version** : voir [`README.en.md`](README.en.md) (golden set préservé).
> 🇫🇷 **Version FR golden set** : [`README.fr.md`](README.fr.md) (préserve l'original FR avant bascule c.1284).

## Description

Composite framework combinant TrendStocks (75 %) avec AllWeather (25 %) via l'Algorithm Framework de QuantConnect. La composante tendance utilise SMA200+EMA20/EMA50 sur 15 large-caps (AAPL/MSFT/GOOGL/AMZN/NVDA/JPM/V/MA/UNH/JNJ/XOM/CVX/HD/PG/KO), AllWeather apporte la diversification statique (SPY 30 % / IEF 30 % / GLD 30 % / XLP 10 %).

## Mesure QC Cloud (#19393, 2026-10-06)

L'évaluation [#19393](https://github.com/jsboige/CoursIA/issues/19393) a rejoué ce code dans le projet [`TrendWeatherPointInTime`](../TrendWeatherPointInTime/), qui reprend le signal et la construction ; avec `universe=fixed`, c'est la règle de ce dossier.

- **Le chiffre publié se reproduit sur sa fenêtre.** Sur 2015-01-01 → 2025-12-31, QC Cloud rend Sharpe 1,15, CAGR 27,1 % et pire baisse 27,6 %. La PSR est de 55,7 %, et non de 77,9 % comme dans le registre comparatif. L'hypothèse d'un Sharpe effectif de 0,6 à 0,9, que ce README avançait auparavant, est réfutée.
- **Le défaut est la liste.** Les 15 titres ont été choisis en 2026. Remplacés chaque mois par les 15 plus grandes capitalisations connues à cette date, la règle perd 0,18 de Sharpe sur 2018-01-01 → 2026-09-25 (1,05 contre 1,22, séries du rejeu en ombre, taux sans risque nul). NVDA, présent dans la liste dès 2018, porte 49 % du résultat des positions fermées de la poche tendance.
- **Verdict préinscrit : `NO BEATS`.** Contre SPY détenu et le 60/40, les différences de Sharpe sont positives mais non significatives (p Holm 0,31), et négatives sur 2024 → 2026-09.

Tableaux, diagnostics et traces : [README de l'évaluation](../TrendWeatherPointInTime/README.md#résultats).

## Balayage de l'allocation (#25533, 2026-11-09)

`main.py` lit la part de la poche tendance dans le paramètre QC `trend_alloc` (défaut 0,75) ; la poche AllWeather prend le reste. Le balayage T60 → T80 de la docstring a été rejoué sur QC Cloud, dans l'espace de backtest du cours, sur 2015-01-01 → 2025-12-31. Le témoin est SPY détenu, avec la même fenêtre, le même courtier et le même capital de départ (projet QC 39161857).

| Allocation | Sharpe | CAGR | Pire baisse | Bêta | Volatilité annuelle | PSR |
|---|---|---|---|---|---|---|
| T60 / AW40 | 1,120 | 23,4 % | 24,5 % | 0,683 | 0,127 | 53,5 % |
| T65 / AW35 | 1,131 | 24,7 % | 25,6 % | 0,711 | 0,134 | 54,5 % |
| T70 / AW30 | 1,140 | 25,9 % | 26,6 % | 0,740 | 0,140 | 55,2 % |
| **T75 / AW25 (défaut)** | **1,148** | **27,1 %** | **27,6 %** | **0,769** | **0,148** | **55,7 %** |
| T80 / AW20 | 1,156 | 28,4 % | 28,7 % | 0,798 | 0,155 | 56,1 % |
| SPY détenu (témoin, même fenêtre 2015-01-01 → 2025-12-31) | 0,537 | 13,4 % | 33,5 % | 0,994 | 0,147 | 2,5 % |

- **Le défaut est inchangé.** Le backtest sans paramètre rend les 27 statistiques du backtest T75. Il reproduit aussi la mesure du 2026-10-26 (section « Non-régression » plus bas) et celle de #19393.
- **La docstring d'origine se confirme à la marge.** Le commit `fa122ae7e` (2026-03-09) annonçait la même pire baisse à 0,1 point près, un Sharpe plus haut de 0,007 à 0,010 et un CAGR plus haut de 0,3 à 0,4 point. Son code ne fixait pas de date de fin : le backtest courait jusqu'à sa date d'exécution. Cette différence de fenêtre est la cause probable de l'écart ; aucun rejeu ne l'a vérifiée.
- **Ces chiffres ont d'abord été publiés sans backtest tracé.** Avant la mesure de #19393 et ce balayage, ce README tenait le Sharpe 1,155 de la docstring pour une affirmation que rien ne permettait de reproduire dans le dépôt (drainage #9434). Les identifiants de backtest du balayage sont consignés dans la PR #25541.
- **Le balayage est monotone.** Chaque pas de 5 points vers la poche tendance ajoute environ 0,009 de Sharpe, 1,1 point de pire baisse et 0,029 de bêta. La plage ne contient pas d'optimum : T75 est un choix de risque. La docstring d'origine le justifiait par un bêta qui dépasserait 0,80 au-delà ; la mesure ne le confirme pas, le bêta reste sous 0,80 jusqu'à T80 (0,798).
- **À T75, la volatilité annuelle égale celle de SPY détenu** (0,148 contre 0,147). À volatilité égale, la composite rend 27,1 % par an contre 13,4 %, pour une pire baisse de 27,6 % contre 33,5 %.
- **Le biais de #19393 reste entier.** La liste des 15 titres a été choisie en 2026, et le balayage ne corrige pas cette lecture du futur. Le verdict contre SPY détenu et le 60/40 reste `NO BEATS`.

## Recherche locale (construction différente)

`quantbook.ipynb` (Lean CLI Docker) et `iter4_research.py` (yfinance) explorent une autre construction que `main.py` : défaut 50/50, poids égaux entre titres haussiers dans `build_composite_weights` (`In [4]`) au lieu de la pondération par le momentum 3 mois de `TrendStocksAlpha`, rééquilibrage hebdomadaire par défaut au lieu de 31 jours, et pas de frais à la §3. Leurs chiffres ne se comparent pas au tableau précédent.

| Source | Sharpe | CAGR | Pire baisse | Allocation | Période et remarque |
|--------|--------|------|-------|-----------|---------|
| `iter4_research.py` (yfinance) | n/a (script) | n/a | n/a | grille 5×5×3 | 2014-2026 ; le script avertit lui-même (ligne 176) : « Simulation Sharpe is typically 2-3x cloud Sharpe » |
| `quantbook.ipynb` `In [5]`, §3 (défaut 50/50) | 0.680 | 10.88 % | -23.53 % | T50 / AW50 | 2015-2026 |
| `quantbook.ipynb` `In [8]`, §4 (balayage d'allocation) | 0.382 → 0.738 | 7.22 % → 14.02 % | -33.72 % → -17.29 % | T0/T10/.../T100, sans T75 | 2015-2026 |
| `quantbook.ipynb` `In [9]`, §5 (balayage de stop-loss) | 0.684 → 2.124 ⚠️ | 10.93 % → 21.29 % | -23.53 % → -4.86 % | T50/AW50 + stop-loss | 2015-2026 ; le stop à 5 % (2.124) est suspect de surajustement |
| `quantbook.ipynb` `In [11]`, §8 (fréquence de rééquilibrage) | 0.619 → 1.070 | 9.92 % → 16.13 % | -23.53 % → -23.94 % | T50/AW50, hebdomadaire / bimensuel / mensuel | 2015-2026 |
| `quantbook.ipynb` `In [12]`, §8 (allocation × fréquence, frais de 5 pb) | 0.544 → 1.239 | 8.90 % → 19.60 % | -27.88 % → -19.43 % | T30→T70 × W/2W/M | 2015-2026 ; le mensuel l'emporte à chaque allocation |

Dans `In [11]`, la même stratégie rééquilibrée chaque mois ou chaque semaine donne un Sharpe de 1.064 ou de 0.674, frais de 5 pb compris : un rééquilibrage moins fréquent réduit la rotation et laisse courir les tendances. `main.py` rééquilibre tous les 31 jours.

## Comment exécuter

**Lean CLI (recherche locale, défaut 50/50) :** `lean research "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_TrendWeather" --notebook quantbook.ipynb`
**Lean CLI (backtest de `main.py`) :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_TrendWeather"` exécute la composite en T75/AW25 ; `--parameter trend_alloc 0.6` fait varier la part de la poche tendance. Le défaut 50/50 n'existe que dans le quantbook.
**QC Cloud :** projet 38458884 de l'espace de backtest du cours, avec la bibliothèque `SharedPCM` attachée (geste « Add Library », cf README de `SharedPCM`). Ailleurs : créer un projet, y attacher `SharedPCM`, copier `main.py` et `alpha_models.py`. Le paramètre `trend_alloc` se règle à chaque backtest (paramètres du projet, ou argument `parameters` de l'API).

## Fichiers

- `main.py` — Stratégie composite v1.5 (T75/AW25 par défaut, part de la poche tendance réglable par le paramètre `trend_alloc`, rééquilibrage tous les 31 jours, frais IBKR). Sa docstring de classe porte le balayage mesuré le 2026-11-09.
- `alpha_models.py` — TrendStocksAlpha (momentum-weighted) + AllWeatherAlpha (static)
- `SharedPCM/pouches_pcm.py` (bibliothèque de projet QC) — `MultiStrategyPouchesPCM`, PCM par poches canonique importé par `main.py` (extraction #19821 brique 1)
- `iter4_research.py` — Recherche yfinance locale (avertit 2-3× overstate cloud Sharpe, ligne 176)
- `quantbook.ipynb` — Recherche Lean CLI Docker : 50/50 default + sweeps (allocation, stop-loss, rebalance freq, T×freq) avec outputs préservés

## Non-régression du module partagé (#20188)

Depuis #21134, `main.py` importe `MultiStrategyPouchesPCM` de `SharedPCM/pouches_pcm.py` au lieu de la copie locale `portfolio_construction.py`. Deux backtests QC Cloud du 2026-10-26, aux paramètres par défaut et sur la fenêtre 2015-01-01 → 2025-12-31, vérifient que ce changement ne modifie aucun ordre :

- **A** : le code de `main` au commit `54f9b9eec1`, avec le module partagé ;
- **B** : les mêmes `main.py` et `alpha_models.py`, avec l'ancienne copie `portfolio_construction.py` prise au commit qui précède la migration (`777f502a2a^`). Les deux arguments que l'ancienne copie ne connaît pas (`additive=True`, `algorithm=self`) sont retirés de l'appel. Les deux tranches n'ont aucun titre en commun : `additive=True` ne doit donc rien changer, et c'est ce que la mesure vérifie.

A et B portent la même instrumentation, qui ne passe aucun ordre. Elle relève la valeur du portefeuille chaque jour à minuit, période de chauffe comprise (270 séances). En fin de backtest, elle calcule une empreinte SHA-256 par année des ordres (identifiant, date, titre, quantité, statut, prix) et des valeurs relevées.

| | A (module partagé) | B (ancienne copie) |
|---|---|---|
| Ordres | 2 094 | 2 094 |
| Valeurs relevées | 4 410 | 4 410 |
| Dernière valeur relevée | 1 408 249,00 | 1 408 249,00 |
| Sharpe (QC) | 1,148 | 1,148 |
| CAGR | 27,121 % | 27,121 % |
| Pire baisse | 27,6 % | 27,6 % |

Les empreintes annuelles sont égales : 12 sur 12 pour les ordres, 13 sur 13 pour les valeurs. Les 27 statistiques de QC sont égales, rotation comprise. La migration ne change donc pas le comportement du projet. Traces hors dépôt : `QC-traces/20188-nr/`.

## Références

- Commit `fa122ae7e` (2026-03-09, jsboige + Claude Opus) — ajout initial de la stratégie ; son message déclare « Iterated from v1.0 (Sharpe 0.622) to v1.5 (Sharpe 1.155) ». Son balayage, sans date de fin, est rejoué par #25533.
- Docstring de `FrameworkCompositeStrategy` (`main.py`) — balayage T60 → T80 mesuré sur QC Cloud le 2026-11-09, avec le témoin SPY détenu.
- [#19393](https://github.com/jsboige/CoursIA/issues/19393) — évaluation à liste datée ([`TrendWeatherPointInTime`](../TrendWeatherPointInTime/)), verdict `NO BEATS`.
- `iter4_research.py:176` — avertissement explicite « Simulation Sharpe typically 2-3× cloud Sharpe ».
- `quantbook.ipynb` cellules `In [5]`, `In [8]`, `In [9]`, `In [11]` et `In [12]` — simulation 50/50 puis balayages d'allocation, de stop-loss, de fréquence et d'allocation × fréquence, avec sorties préservées.
- #1621 (EPIC de drainage — prose mesurée contre prose périmée dans le dépôt)
- #9434 (umbrella de drainage — nettoyage multi-PR des README périmés)

# CTG Momentum (C#) (ID: 19225388)

Stratégie momentum avec indicateurs custom avancés en C#.

## Performance (post-bugfix SMA200)

- **Période** : 2015-01-01 → 2025-12-31, bornes figées dans `Main.cs` et exposées en paramètres QC `start-date` et `end-date` (#22541)
- **Backtest C# sur QC Cloud** (univers OEF, filtre capital-gain OFF) : Sharpe 0.438, CAGR 14.0 %, drawdown max 42.4 %, 888 ordres ; identifiants dans la section « Retest QC500 »
- **Proxy Python du carnet de recherche**, même fenêtre : Sharpe 1,106 (30 grandes capitalisations, sans frais). L'écart avec le backtest C# est discuté dans `RESEARCH_SUMMARY.md`.

## Fichiers

### Code Principal

- `Main.cs` - StocksOnTheMoveAlgorithm, OEF ETF universe
- `CustomMomentumIndicator.cs` - Indicateur composite (slope + MA + gap + ATR)
- `AnnualizedExponentialSlopeIndicator.cs` - Régression exponentielle annualisée
- `GapIndicator.cs` - Détection de gaps
- `MarketRegimeFilter.cs` - Filtre régime SPY > SMA200

### Recherche

- `RESEARCH_SUMMARY.md` - Analyse robustesse 2015-2025 (Feb 2026)
- `research_robustness_simple.py` - Script Python backtest étendu
- `research_robustness_charts.png` - Visualisations régime filter + walk-forward
- `research_results.txt` - Output complet backtest
- `research_robustness.ipynb` - Notebook Jupyter exécuté (yfinance, fenêtre figée 2015-2025) : régime SMA(200), backtest proxy, sensibilité de la SMA, stabilité par semestre

## Concepts enseignes

- Custom indicators en C# (WindowIndicator, TradeBarIndicator)
- MathNet.Numerics (régression linéaire, R-squared)
- Market régime filtering (SMA 200)
- ATR-based position sizing
- Stabilité par sous-périodes (découpage semestriel à règles fixes)
- Fenêtre de backtest figée et paramétrée : sous-périodes mesurées depuis une seule compilation
- Robustness testing sur 10+ ans

## Bugfix Important (Feb 2026)

**Bug**: SMA period = 10 au lieu de 200 (indicateur de régime `SMA("SPY", 200)` de `Main.cs`)
**Impact**: ~95% Risk-ON (trop agressif) → 76.8% Risk-ON (optimal)
**Status**: Corrigé ; backtest cloud sur la fenêtre figée : Sharpe 0.438 (univers OEF), au-dessus du seuil 0.4 de `RESEARCH_SUMMARY.md`

## Prochaines Étapes

1. Mesurer séparément ce qui sépare le proxy Python (Sharpe 1,106) du backtest C# (0.438) : liste de 30 titres choisie en 2026, concentration du proxy (1,9 position en moyenne), définition du momentum
2. Ramener le drawdown sous 35 % et le CAGR au-dessus de 15 %, les deux critères de `RESEARCH_SUMMARY.md` que le backtest C# ne tient pas sur la fenêtre figée (42.4 % et 14.0 %)

## Filtre capital-gain (#12034, consolidation QC research 21160)

**Source primaire** : Cannon & Lynch (2025), *Return Extrapolation and Dividends*, Review of
Finance 29(4), 1009-1042 (l'article QC cite le SSRN 3816782 ; la version publiée RoF est la
référence canonique). Claim : l'extrapolation des rendements — et donc la prime de momentum —
se concentre dans les actions qui ne paient pas de dividende (« capital-gain stocks »,
1,417 %/mois vs 0,684 % chez les payeurs, écart non expliqué par les factor models standards).

**Implémentation** : flag `_filterDividendPayers` dans `Main.cs` (défaut OFF = baseline
inchangée). Quand ON, le classement hebdomadaire exclut toute action ayant distribué au moins
un dividende sur les 365 derniers jours (`History<Dividend>` rafraîchi chaque semaine, cache
`_paysDividend`). Motivation : donner au projet le pattern filtre-de-sélection factoriel du
cours, à côté du `MarketRegimeFilter` existant — même emplacement logique (pré-sélection dans
l'événement planifié), même approche de flag opt-in.

**Comparaison honnête 2015-2025** (projet QC Cloud 38433791, fenêtre figée 2015-01-01 →
2025-12-31, même compilation pour les deux bras, mêmes coûts IB ; identifiants dans la section
suivante) :

| Bras                        | Sharpe | CAGR   | MaxDD  | Ordres |
|-----------------------------|--------|--------|--------|--------|
| Baseline (filtre OFF)       | 0.438  | 14.0 % | 42.4 % | 888    |
| Capital-gain (filtre ON)    | 0.333  | 9.3 %  | 24.7 % | 452    |

**Verdict : NO BEATS**, confirmé sur la fenêtre figée (#22541). Sur CE moteur (slope 90 j +
régime SPY > SMA200, univers OEF S&P 100), le filtre capital-gain dégrade Sharpe et rendement —
mais divise le drawdown (42 → 25 %) et le turnover (888 → 452 ordres). Les chiffres publiés
auparavant pour ces deux bras (Sharpe 0.451 et 0.259, 961 et 458 ordres) venaient d'une fenêtre
qui se terminait à la date d'exécution : voir la fin de la section suivante. L'écart avec l'article (Sharpe 0.602 sur 1 000 actions, momentum
12-1 mensuel à breakpoints NYSE) est instructif : le claim Cannon-Lynch porte sur le momentum
canonique à formation mensuelle, pas sur le slope journalier 90 j. L'univers OEF (S&P 100,
grandes capitalisations payant majoritairement des dividendes) est aussi le terrain le moins
favorable au filtre — l'article opère sur les 1 000 plus liquides NYSE+NASDAQ+AMEX où les
capital-gain stocks sont bien représentées. Le filtre reste pédagogiquement pertinent (pattern
factoriel documenté + gestion du risque) et le flag OFF préserve la baseline ; le terrain
naturel pour le retester serait un univers élargi (QC500) — retest livré ci-dessous (#11698).

Sources : QuantConnect research 21160 (*Momentum in Capital-Gain Stocks*, lastmod 2026-08-17) ;
verdict CONSOLIDATION documenté sur l'issue #12034 (lecture analytique + filtre du bouquet —
aucun des 12 projets momentum existants n'excluait les payeurs de dividendes).

## Retest QC500 (#11698, grain de suivi de #12034)

L'hypothèse ouverte laissée par #12034 — « l'univers OEF (S&P 100, grandes caps
majoritairement dividendifères) est le terrain le moins favorable au filtre, le retester sur
un univers élargi » — est désormais tranchée : **toujours NO BEATS, et l'écart se creuse**.

**Implémentation** : le sélecteur d'univers devient un paramètre QC (`[Parameter("universe")]`,
défaut `OEF` = baseline inchangée). La valeur `QC500` opt-in branche `Universe.QC500` — dans
LEAN actuel, cet univers sélectionne chaque mois les 500 actions US les plus liquides par
dollar-volume et hérite des `UniverseSettings` du projet, ici résolution Daily. Il ne reproduit
pas la liste des constituants du S&P 500. Le filtre capital-gain devient
lui aussi un paramètre (`filter-dividend-payers`), si bien que **les quatre bras proviennent de
backtests paramétrés d'une seule et même compilation** — chaque run loge sa configuration
active en `Debug` dans `Initialize`, preuve firsthand de l'arm exécuté.

**Comparaison honnête 4 bras** (projet QC Cloud 38433791, même compilation, fenêtre figée
2015-01-01 → 2025-12-31 soit 2 766 dates tradables par bras, mêmes coûts IB, même moteur :
slope 90 j + régime SPY > SMA200 + top-20 hebdo + sizing ATR 1 %) :

| Univers                            | Filtre capital-gain | Sharpe | CAGR     | MaxDD  | Ordres |
|------------------------------------|---------------------|--------|----------|--------|--------|
| OEF (S&P 100)                      | OFF (baseline)      | 0.438  | 13.997 % | 42.4 % | 888    |
| OEF (S&P 100)                      | ON                  | 0.333  | 9.298 %  | 24.7 % | 452    |
| QC500 (top-500 dollar-volume LEAN) | OFF                 | 0.307  | 9.862 %  | 58.8 % | 1 523  |
| QC500 (top-500 dollar-volume LEAN) | ON                  | 0.071  | 2.403 %  | 42.7 % | 831    |

*Comptes d'ordres relevés via l'API QC (`/backtests/orders/read`, tous les ordres paginés) ;
profits nets respectifs +322,9 %, +166,1 %, +181,6 % et +29,9 %. Le filtre divise le nombre
d'ordres par 2,0 sur OEF et par 1,8 sur QC500.*

**Sous-périodes, filtre OFF** (même compilation ; chaque sous-période repart du capital initial,
indicateurs préchauffés sur 200 jours avant la date de début par `SetWarmUp(200)`) :

| Univers | Fenêtre                 | Dates | Sharpe | CAGR     | MaxDD  | Ordres |
|---------|-------------------------|-------|--------|----------|--------|--------|
| OEF     | 2015-01-01 → 2019-12-31 | 1 258 | 0.476  | 12.916 % | 33.9 % | 332    |
| OEF     | 2020-01-01 → 2025-12-31 | 1 508 | 0.445  | 15.797 % | 42.4 % | 575    |
| QC500   | 2015-01-01 → 2019-12-31 | 1 258 | 0.111  | 2.351 %  | 41.1 % | 612    |
| QC500   | 2020-01-01 → 2025-12-31 | 1 508 | 0.473  | 18.171 % | 45.2 % | 921    |

**Verdict : NO BEATS — et le verdict OEF se généralise en avertissement.** Trois lectures :

1. **Effet univers seul** (filtre OFF, OEF → QC500) : sur la fenêtre entière, QC500 est moins
   bon sur les trois mesures (Sharpe 0.438 → 0.307, CAGR 13.997 → 9.862 %, drawdown 42.4 →
   58.8 %). Les sous-périodes montrent que cet effet n'est pas stable : QC500 est très en retrait
   sur 2015-2019 (Sharpe 0.111 contre 0.476), puis légèrement au-dessus d'OEF sur 2020-2025
   (0.473 contre 0.445, CAGR 18.171 contre 15.797 %) avec un drawdown plus profond (45.2 contre
   42.4 %). L'élargissement de l'univers n'améliore pas le couple rendement-risque.
2. **Effet filtre sur QC500** : forte dégradation — Sharpe 0.307 → 0.071 et CAGR 9.862 →
   2.403 %. Le backtest établit cette dégradation sur l'univers élargi ; il ne permet pas, à lui
   seul, de l'attribuer à un sous-groupe précis de titres ou à un épisode de marché particulier.
3. **La réduction de drawdown se retrouve sur QC500, à un prix bien plus élevé** : le filtre
   retire un nombre de points comparable sur les deux univers (42.4 → 24.7 % sur OEF, 58.8 →
   42.7 % sur QC500), mais il divise le CAGR par 4,1 sur QC500, contre 1,5 sur OEF, et le Sharpe
   baisse sur les deux. Le bénéfice de risque se paie en rendement, et ce prix dépend du terrain :
   il ne peut pas être présenté comme une propriété stable du filtre.

**Lecture épistémique** (la leçon pédagogique centrale du grain) : le claim de Cannon & Lynch
(2025, *Review of Finance* 29(4) — source primaire citée en tête de la section #12034) est
mesuré sur SON protocole : momentum 12-1 mensuel canonique, breakpoints NYSE, 1 000 plus
liquides. Deux terrains distincts du nôtre — OEF (S&P 100) et QC500 (top-500 US par
dollar-volume) en slope journalier 90 j à seuil 10 % — ne reproduisent pas ce résultat.
**Transférer le filtre sans transférer le
protocole ne reproduit pas le claim** : un facteur de sélection comportemental est indexé à la
définition du momentum qui l'a produit. Le pattern paramétré reste au catalogue (4 bras
reproductibles depuis un seul build), la baseline OEF reste le défaut du dépôt.

Identification des runs (projet QC Cloud 38433791, compilation
`f708087c1d99f41b2ffa4f139202bb5a-4682d9d927f980b3320bc7044ad67346`, paramètres QC `universe`,
`filter-dividend-payers`, `start-date` et `end-date`) :

- OEF OFF : `22541-full-oef-off` (`4eafc2efb11c9933b1937b986ab24597`) ;
- OEF ON : `22541-full-oef-on` (`9b1cacb519ebe9a00c5fbe088f97bf26`) ;
- QC500 OFF : `22541-full-qc500-off` (`47d1d6fa38d3409c17ab2d4a95c6f271`) ;
- QC500 ON : `22541-full-qc500-on` (`fb46cf1be3e298db59952ee082a7170a`) ;
- sous-périodes, filtre OFF : `22541-p1-oef-off` (`0e478ab9905dcd1742648ff57129635f`),
  `22541-p2-oef-off` (`0c26280ff30b5e8541aeaf6999b0d969`), `22541-p1-qc500-off`
  (`0a2b672d776cbad6348b53c6504322ee`) et `22541-p2-qc500-off` (`cadcb5e055fff835963d4fdfc849a397`).

**D'où venaient les chiffres publiés auparavant.** Les quatre runs précédents (projet 35425281,
compilation `57d3f236…`) se terminaient à la date d'exécution et couvraient 2 930 dates, jusqu'en
2026-08. Le code de stratégie n'a pas changé depuis : seules les bornes de la fenêtre et la ligne
de `Debug` qui les affiche diffèrent. Trois contrôles, lancés depuis la compilation ci-dessus :

- un rejeu du bras QC500 OFF sur la fenêtre figée (`22541-rep-qc500-off`,
  `642613c9dd57b8ffc6391a54188891f1`) redonne exactement le même résultat (1 523 ordres, mêmes
  métriques) : l'écart ne vient pas d'une variation d'un run à l'autre ;
- le bras OEF OFF prolongé jusqu'au 2026-07-24, dernière date acceptée par le projet à la date de
  mesure (`22541-ext-oef-off`, `19ab35fb39d6f68b9815734b37142cc7`, 2 906 dates), donne Sharpe
  0.479, CAGR 15.663 %, drawdown 42.4 %, 957 ordres et +438,5 % : les sept premiers mois de 2026
  rapprochent les chiffres des anciens (0.445, 981 ordres, +401,4 %). La part restante n'est pas
  attribuée : elle peut venir des dernières semaines de l'ancienne fenêtre, que le projet
  n'accepte plus, ou d'une révision des prix ajustés entre les deux mesures ;
- le bras QC500 OFF prolongé de la même façon (`22541-ext-qc500-off`,
  `17005cf55dcfb54b57690a8d887470f5`, 2 906 dates) donne Sharpe 0.374, CAGR 12.740 %, drawdown
  58.8 %, 1 604 ordres et +300,4 %. Les anciens chiffres étaient 0.459, 16.682 %, 58.8 %, 1 638
  ordres et +504,6 %. Le prolongement en 2026 ne comble qu'une partie de l'écart : le reste n'est
  pas attribué. Sur QC500, une source possible de plus est la composition de `Universe.QC500`,
  recalculée chaque mois à partir des données du moment.

Les chiffres de la fenêtre figée sont donc ceux à citer : ils ne bougeront plus d'une exécution à
l'autre.

# CTG Momentum (C#) (ID: 19225388)

Stratégie momentum avec indicateurs custom avancés en C#.

## Performance (post-bugfix SMA200)

- **Période**: 2021-01-01 → Now
- **Sharpe**: 0.507
- **Recommandation recherche**: Étendre a 2015-01-01 (Sharpe attendu: 1.05)

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
- `research_robustness.ipynb` - Notebook Jupyter (QuantBook, non execute)

## Concepts enseignes

- Custom indicators en C# (WindowIndicator, TradeBarIndicator)
- MathNet.Numerics (régression linéaire, R-squared)
- Market régime filtering (SMA 200)
- ATR-based position sizing
- Walk-forward validation
- Robustness testing sur 10+ ans

## Bugfix Important (Feb 2026)

**Bug**: SMA period = 10 au lieu de 200 (ligne 119)
**Impact**: ~95% Risk-ON (trop agressif) → 76.8% Risk-ON (optimal)
**Status**: Corrige, a valider par backtest cloud

## Prochaines Étapes

1. Modifier `Main.cs`: `SetStartDate(2015, 1, 1)`
2. Compiler via QC cloud
3. Lancer backtest via web UI
4. Valider Sharpe >= 0.4 sur période étendue

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

**Comparaison honnête 2015-2025** (même projet QC Cloud 35425281, même période, mêmes coûts IB) :

| Bras                        | Sharpe | CAGR   | MaxDD  | Ordres |
|-----------------------------|--------|--------|--------|--------|
| Baseline (filtre OFF)       | 0.451  | 15.0 % | 42.4 % | 961    |
| Capital-gain (filtre ON)    | 0.259  | 7.9 %  | 24.7 % | 458    |

**Verdict : NO BEATS.** Sur CE moteur (slope 90 j + régime SPY > SMA200, univers OEF S&P 100),
le filtre capital-gain dégrade Sharpe et rendement — mais divise le drawdown (42 → 25 %) et le
turnover (961 → 458 ordres). L'écart avec l'article (Sharpe 0.602 sur 1 000 actions, momentum
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

**Comparaison honnête 4 bras** (même projet QC Cloud 35425281, même compilation, 2 930
jours tradables par bras, 2015-01-01 → 2026-08, mêmes coûts IB, même moteur : slope 90 j +
régime SPY > SMA200 + top-20 hebdo + sizing ATR 1 %) :

| Univers            | Filtre capital-gain | Sharpe | CAGR    | MaxDD  | Ordres |
|--------------------|---------------------|--------|---------|--------|--------|
| OEF (S&P 100)      | OFF (baseline)      | 0.445  | 14.825 % | 42.4 % | 981    |
| OEF (S&P 100)      | ON                  | 0.258  | 7.903 %  | 24.7 % | 458    |
| QC500 (top-500 dollar-volume LEAN) | OFF        | 0.459  | 16.682 % | 58.8 % | 1 638  |
| QC500 (top-500 dollar-volume LEAN) | ON         | 0.011  | 1.097 %  | 52.3 % | 882    |

*Comptes d'ordres relevés via l'API QC (`totalOrders`) ; valeurs non nulles, cohérentes avec
les profits nets respectifs (+401,4 %, +142,8 %, +504,6 % et +13,6 %). Le filtre divise le
nombre d'ordres par 2,1 sur OEF et par 1,9 sur QC500.*

**Verdict : NO BEATS — et le verdict OEF se généralise en avertissement.** Trois lectures :

1. **Effet univers seul** (filtre OFF, OEF → QC500) : Sharpe proche (0.445 → 0.459) et CAGR en
   hausse (14.825 → 16.682 %), mais drawdown également accru (42.4 → 58.8 %). Ces sorties ne
   montrent donc pas d'amélioration du couple rendement-risque par le seul élargissement.
2. **Effet filtre sur QC500** : forte dégradation — Sharpe 0.459 → 0.011 et CAGR 16.682 →
   1.097 %. Le backtest établit cette dégradation sur l'univers élargi ; il ne permet pas, à lui
   seul, de l'attribuer à un sous-groupe précis de titres ou à un épisode de marché particulier.
3. **La réduction de drawdown observée sur OEF ne se généralise pas dans la même ampleur** :
   42.4 → 24.7 % sur OEF, contre 58.8 → 52.3 % sur QC500. Le bénéfice de risque dépend donc au
   minimum du terrain testé et ne peut pas être présenté comme une propriété stable du filtre.

**Lecture épistémique** (la leçon pédagogique centrale du grain) : le claim de Cannon & Lynch
(2025, *Review of Finance* 29(4) — source primaire citée en tête de la section #12034) est
mesuré sur SON protocole : momentum 12-1 mensuel canonique, breakpoints NYSE, 1 000 plus
liquides. Deux terrains distincts du nôtre — OEF (S&P 100) et QC500 (top-500 US par
dollar-volume) en slope journalier 90 j à seuil 10 % — ne reproduisent pas ce résultat.
**Transférer le filtre sans transférer le
protocole ne reproduit pas le claim** : un facteur de sélection comportemental est indexé à la
définition du momentum qui l'a produit. Le pattern paramétré reste au catalogue (4 bras
reproductibles depuis un seul build), la baseline OEF reste le défaut du dépôt.

Identification des quatre runs de la compilation
`57d3f236058b6004d8c63b4d87700ae0-60194a281bf542c7da061efacd170add` :

- OEF OFF : `11698-OEF-filterOFF-fresh` (`87d39d8edc720f31ef3a0e30a2f9876a`) ;
- OEF ON : `11698-OEF-filterON-fresh` (`27c1341918038c4866622fe943fda7d7`) ;
- QC500 OFF : `11698-QC500-filterOFF` (`13b95feeba1db7808c941d944a753baf`) ;
- QC500 ON : `11698-QC500-filterON` (`03393f901654372c2d5820dd6692d713`).

Chaque run couvre 2 930 dates tradables sur la même fenêtre 2015-01-01 → now.

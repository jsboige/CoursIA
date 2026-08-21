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
naturel pour le retester serait un univers élargi (QC500), grain séparé.

Sources : QuantConnect research 21160 (*Momentum in Capital-Gain Stocks*, lastmod 2026-08-17) ;
verdict CONSOLIDATION documenté sur l'issue #12034 (lecture analytique + filtre du bouquet —
aucun des 12 projets momentum existants n'excluait les payeurs de dividendes).

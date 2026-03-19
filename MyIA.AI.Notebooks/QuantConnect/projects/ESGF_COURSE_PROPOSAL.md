# ESGF QC Trading - Proposition Structure Cours

**Date**: 2026-03-14
**Deadline**: Fin mars 2026
**Contexte**: Partenariat avec Jared Broad (CEO QuantConnect)
**Issue**: #53

---

## 1. Audit des Stratégies - Sélection ESGF

### Stratégies Recommandées (15)

| Module | Stratégie | Sharpe | Niveau | Research | QC ID |
|--------|-----------|--------|--------|----------|-------|
| **M1-Bases** | EMA-Cross-Stocks | 0.872 | Debutant | — | — |
| | AllWeather | 0.667 | Debutant | yfinance | — |
| | EMA-Cross-Index | 0.470 | Debutant | yfinance | — |
| **M2-Momentum** | SectorMomentum | 0.621 | Intermediaire | yfinance | — |
| | FamaFrench | 0.540 | Intermediaire | yfinance | — |
| | MomentumStrategy | 0.565 | Intermediaire | yfinance | — |
| | TrendStocksLite | 0.719 | Intermediaire | — | — |
| **M3-Framework** | EMA-Cross-Alpha | 0.996* | Intermediaire | — | 28885488 |
| | TrendStocks-Alpha | 0.609* | Intermediaire | — | 28885507 |
| | Framework_Composite_EMATrend | 0.867* | Avance | QuantBook | 28911253 |
| **M4-Advanced** | Framework_Composite_TrendWeather | 1.155 | Avance | QuantBook | — |
| | RegimeSwitching | 0.553 | Avance | — | — |
| | AdaptiveAssetAllocation | 0.518 | Avance | — | — |
| **M5-Options** | Option-Wheel | 0.996 | Avance | QuantBook | — |
| | Options-VGT | 0.507 | Avance | — | — |
| **M6-Crypto** | EMA-Cross-Crypto | 1.272 | Debutant | yfinance | — |

\* SESSION 5 results (2020-2025 backtests)

### Stratégies à Éviter (8)

| Stratégie | Sharpe | Raison |
|-----------|--------|--------|
| Multi-Layer-EMA | 0.928 | Non robuste (Sharpe 0.38 hors bulle) |
| OptionsIncome | 0.234 | Alpha structurellement faible |
| TurnOfMonth | 0.128 | Effet calendar faible |
| VIX-TermStructure | 0.051 | SVXY affaibli post-VIXplosion |
| TrendFilteredMeanReversion | -0.016 | Trop rare (~9 trades/an) |
| ForexCarry | -0.324 | Carry prime evaporee |
| PairsTrading | -0.361 | Cointegration instable |
| ETF-Pairs | -0.706 | Échec technique |

---

## 2. Structure de Cours

### Module 1: Bases (Semaine 1-2)

- Introduction QC + EMA Crossover
- Portfolio Construction (AllWeather)
- Indicateurs avancés (EMA-Cross-Index)
- TP noté

### Module 2: Momentum (Semaine 3-4)

- Dual Momentum (SectorMomentum)
- Factor Investing (FamaFrench)
- Rotation ETFs (MomentumStrategy)
- TP noté

### Module 3: Algorithm Framework (Semaine 5-7)

- AlphaModel Pattern (EMA-Cross-Alpha)
- Risk-Adjusted Momentum (TrendStocks-Alpha)
- PortfolioConstructionModel (MultiStrategyPCM)
- Composite AlphaModel (Framework_Composite_EMATrend)
- QuantBook Research
- Projet noté

### Module 4: Composite Avancées (Semaine 8-9)

- TrendWeather Composite
- Regime Switching
- Adaptive Asset Allocation
- Optimisation Paramétrique

### Module 5: Options (Semaine 10) - Optionnel

- Wheel Strategy
- Multi-Stock Covered Calls

### Module 6: Crypto (Semaine 11) - Optionnel

- EMA Crossover Crypto
- Spécificités Binance Cash

---

## 3. Gap Analysis

### Sans Notebooks (13 projets)

| Projet | Priorité | Action |
|--------|----------|--------|
| **TrendStocksLite** | HIGH | Créer notebook yfinance |
| **EMA-Cross-Alpha** | HIGH | Dans SESSION5_PATTERNS.md |
| **TrendStocks-Alpha** | HIGH | Dans SESSION5_PATTERNS.md |
| RegimeSwitching | Medium | Optionnel |
| AdaptiveAssetAllocation | Medium | Optionnel |
| Options-VGT | Low | Module 5 optionnel |
| CSharp-BTC-EMA-Cross | Low | Demo C# |
| CSharp-CTG-Momentum | Low | Demo C# |
| DualMomentum | Medium | Contre-exemple |
| RiskParity | Medium | Contre-exemple |
| MeanReversion | Medium | Contre-exemple |
| FuturesTrend | Medium | Contre-exemple |
| Trend-Following | Medium | Contre-exemple |

---

## 4. Actions Requises

### Immédiat (Semaine 11-12 mars)

1. Valider structure cours
2. Créer notebooks gaps (TrendStocksLite)

### Moyen (Semaine 13-17 mars)

3. Créer ESGF_EXERCISES.md
4. Déployer FamaFrench-AllWeather

### Faible (Fin mars)

5. Documentation C# examples

---

## 5. Questions pour Validation

1. La progression M1→M4 est-elle adaptée pour ESGF ?
2. Priorité gaps: Tous les notebooks ou focus SESSION 5 ?
3. Timing: 2 semaines = Priorité absolue quoi ?
4. Partenariat QC: Jared Broad attend-il des livrables spécifiques ?

# QuantConnect Algorithmic Trading Projects

**116 projets** de trading algorithmique sur QuantConnect Cloud. Chaque stratégie illustre un concept pédagogique ; les performances varient volontairement pour montrer ce qui survive au backtest réaliste.

> **Visiteur ?** Lire le [Quick Tour](../QUICK_TOUR.md) (2 min) pour comprendre l'ensemble.

## Classification

| Label | Sharpe | Action |
|-------|--------|--------|
| **Robuste** | > 0.5 | Conserver, itérer |
| **Historique** | 0-0.5 | Contre-exemple, documenter les régimes favorables |
| **Exploratoire** | < 0 | Retravailler si pédagogique |

## Performance Summary

### Robuste (Sharpe > 0.5) — 19 stratégies

| Projet | Sharpe | CAGR | MaxDD | Période | Niveau |
|--------|--------|------|-------|---------|--------|
| [BTC-ML](BTC-ML/) | **1.647** | 38.1% | 48.8% | 2020-2026 | Intermédiaire |
| [Framework_Composite_TrendWeather](Framework_Composite_TrendWeather/) | **1.155** | 27.4% | 27.7% | 2015-2026 | Avancé |
| [CSharp-BTC-EMA-Cross](CSharp-BTC-EMA-Cross/) | **1.094** | 36.2% | 40.7% | 2017-2026 | Débutant |
| [EMA-Cross-Stocks](EMA-Cross-Stocks/) | **0.872** | 25.7% | 35.7% | 2015-2026 | Débutant |
| [Portfolio-Optimization-ML](Portfolio-Optimization-ML/) | **0.896** | 27.6% | 41.6% | 2015-2026 | Avancé |
| [CausalEventAlpha](CausalEventAlpha/) | **0.779** | 16.8% | 22.1% | 2015-2026 | Avancé |
| [Gaussian-Direction-Classifier](Gaussian-Direction-Classifier/) | **0.761** | — | 25.6% | 2015-2026 | Avancé |
| [TrendStocksLite](TrendStocksLite/) | **0.719** | 18.2% | 33.7% | 2015-2026 | Intermédiaire |
| [ML-Temporal-CNN](ML-Temporal-CNN/) | **0.734** | 20.5% | 21.6% | 2019-2024 | Avancé |
| [ML-LLM-Summarization](ML-LLM-Summarization/) | **0.686** | 15.5% | 22.7% | 2015-2026 | Avancé |
| [ML-RandomForest](ML-RandomForest/) | **0.682** | 20.1% | 36.4% | 2015-2026 | Avancé |
| [ML-Trend-Scanning](ML-Trend-Scanning/) | **0.656** | 19.1% | 34.8% | 2015-2026 | Intermédiaire |
| [AllWeather](AllWeather/) | **0.667** | 9.3% | 16.4% | 2010-2026 | Débutant |
| [SectorMomentum](SectorMomentum/) | **0.621** | 13.2% | 22.8% | 2010-2026 | Intermédiaire |
| [BlackLitterman-Momentum](BlackLitterman-Momentum/) | **0.604** | 13.7% | 33.1% | 2015-2026 | Avancé |
| [MomentumStrategy](MomentumStrategy/) | **0.565** | 11.8% | 25.8% | 2010-2026 | Intermédiaire |
| [ML-XGBoost](ML-XGBoost/) | **0.566** | 14.8% | 38.6% | 2015-2026 | Avancé |
| [ML-FeatureEngineering](ML-FeatureEngineering/) | **0.571** | 10.5% | 19.6% | 2015-2026 | Avancé |
| [RegimeSwitching](RegimeSwitching/) | **0.553** | 11.7% | 33.0% | 2008-2026 | Avancé |

### Historique (Sharpe 0-0.5) — 15 stratégies

[Multi-Layer-EMA](Multi-Layer-EMA/) (0.928, non robuste) · [EMA-Cross-Index](EMA-Cross-Index/) (0.470) · [DualMomentumNoTLT](DualMomentumNoTLT/) (0.469) · [Adaptive-Conformal-Risk](Adaptive-Conformal-Risk/) (0.423) · [RiskParity](RiskParity/) (0.399) · [DualMomentum](DualMomentum/) (0.350) · [MeanReversion](MeanReversion/) (0.294) · [BTC-ML](BTC-ML/) (0.282) · [EMA-Cross-Crypto](EMA-Cross-Crypto/) (0.244) · [OptionsIncome](OptionsIncome/) (0.207) · [FuturesTrend](FuturesTrend/) (0.136) · [TurnOfMonth](TurnOfMonth/) (0.128) · [VIX-TermStructure](VIX-TermStructure/) (0.051)

### Exploratoire (Sharpe < 0) — 4 stratégies

[TrendFilteredMeanReversion](TrendFilteredMeanReversion/) (-0.016) · [ForexCarry](ForexCarry/) (-0.324) · [PairsTrading](PairsTrading/) (-0.361) · [ETF-Pairs](ETF-Pairs/) (-0.706)

### ML / DL / RL — 35+ stratégies

Stratégies ML/AI basées sur *Hands-On AI Trading* et implémentations internes. Toutes backtestées sur QC Cloud.

Voir [STRATEGIES_DETAIL.md](STRATEGIES_DETAIL.md#machine-learning--deep-learning--rl-intermediaireavance) pour le catalogue complet.

### QC Strategy Library Clones — 8 projets

Références avancées clonées depuis la QC Cloud Library (avril 2026). Top performer : [LongShortHarvest-QC](LongShortHarvest-QC/) (OOS Sharpe 3.39).

Voir [STRATEGIES_DETAIL.md](STRATEGIES_DETAIL.md#qc-strategy-library-clones-avance) pour le catalogue complet.

---

## Structure d'un Projet

```
MonProjet/
  main.py / Main.cs     # Algorithme (déployé sur QC Cloud)
  alpha.py / helpers     # Modules auxiliaires
  research.ipynb         # Recherche exploratoire
  quantbook.ipynb        # QuantBook (données QC natives, optionnel)
  README.md              # Documentation
```

## Utilisation

**Sur QuantConnect Cloud** : Créer un projet Python → copier `main.py` → lancer le backtest.

**En local** : `pip install yfinance pandas matplotlib` puis `jupyter notebook projects/MonProjet/research.ipynb`

## Ressources

- [Descriptions détaillées](STRATEGIES_DETAIL.md) — Toutes les stratégies par catégorie
- [Leçons et patterns](../../../docs/quantconnect.md) — 20 patterns confirmés + anti-patterns
- [Catalogue QC Cloud](../docs/qc_strategies_catalog.md) — Métriques par stratégie avec Cloud IDs
- [Quick Tour](../QUICK_TOUR.md) — Vue d'ensemble en 2 minutes
- [QuantConnect Lab](https://www.quantconnect.com/terminal) · [Documentation](https://www.quantconnect.com/docs) · [Forum](https://www.quantconnect.com/forum)

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

## État vérifié sous frais réels (#1630, 2018-2025)

> **Caveat important.** Les Sharpes du tableau « Robuste » ci-dessus sont des valeurs **catalogue (pré-frais, fenêtres variables)**. La campagne #1630 a re-vérifié 36+ de ces stratégies sous **frais IBKR réels** (`PercentFeeModel` explicite) sur une **fenêtre alignée 2018-2025**. Plusieurs stars du catalogue **s'effondrent** dans ces conditions — le label « Robuste » ci-dessus ne préjuge pas de la robustesse sous frais réels.

### Effondrements confirmés (catalogue → aligné 2018-2025)

| Stratégie | Sharpe catalogue | Sharpe aligné | Delta | Cause |
|-----------|------------------|---------------|-------|-------|
| HighBookToMarketFScore | 2.09 | **0.41** | -80% | Value/factor écrasé par les frais réels, MaxDD -60% |
| PuppiesOfTheDow | 1.99 | **0.30** | -85% | Value/factor + frais réels |
| ML-Trend-Scanning | 0.66 | **0.33** | -50% | Rebalancement quotidien SPY/TLT/GLD multi-actifs = turnover écrasé |
| AllWeather | 0.67 | **0.47** | -30% | Sleeve bonds/gold multi-actifs = friction de panier |

### Leaders vérifiés alignés (backbone no-ML)

| Stratégie | Sharpe aligné | PSR | Caveat |
|-----------|---------------|-----|--------|
| Framework_Composite_EMATrend | **0.611** | 19.8% | Sleeve EMA 100% Mag7 → biais de survivorship ; Sharpe le plus haut mais constitution concentrée |
| composite-c2-equityfactor | **0.574** | 25.8% | **Constitution la plus robuste** (25 actions factor-diversifiées) ; tient juste au-dessus du seuil |

> **TrendFollowing** (catalogue 1.072) n'est **pas reproductible** depuis le `main.py` du dépôt : le baseline-clone (2015-2024, IBKR) donne un Sharpe bien inférieur (~0.36-0.41, PSR < 9%). Le 1.072 provient d'un état du code cloud antérieur — à citer avec ce caveat (diagnostic finding #18).

### Le discriminateur (leçon durable)

La résistance aux frais **n'est pas** l'asset-class ni ML-vs-indicateur : c'est le **realized-turnover** = fréquence × taille par trade × homogénéité des frais du panier. Un composite equity-only fee-homogeneous en rebalancement mensuel (**c2 0.574**) tient là où un multi-asset rotationnel (**AllWeather 0.47**) s'effondre — même architecture, c'est l'univers qui décide.

Détail complet, comparatifs best-vs-aligned et diagnostics par stratégie : [docs/qc/qc-comparative-backtests.md](../../../docs/qc/qc-comparative-backtests.md) (See #1630).

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

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Ce catalogue de **116 projets** est un **zoo de stratégies backtestées**, organisé non pas par thème mais par **robustesse** (Robuste / Historique / Exploratoire). La classification elle-même est la leçon :

- **La robustesse prime sur le Sharpe brut** : une stratégie à Sharpe 1.6 qui s'effondre hors-échantillon vaut moins qu'une stratégie à Sharpe 0.6 stable à travers les régimes. Le label *Robuste* (> 0.5 soutenu) est la barre pédagogique, pas le chiffre spectaculaire.
- **Les contre-exemples sont aussi importants que les succès** : les stratégies *Exploratoire* (Sharpe < 0) et *Historique* (0-0.5) sont conservées **délibérément** pour montrer *ce qui ne marche pas* et pourquoi — PairsTrading sur ETF corrélés, ForexCarry, MeanReversion naïf. On apprend autant d'un edge négatif bien diagnostiqué que d'un edge positif.
- **La diversité des régimes compte** : un projet backtesté 2015-2026 (bull/bull) n'a pas la même valeur probante qu'un projet backtesté 2008-2026 (incluant le GFC). La colonne *Période* est lue comme un indice de robustesse, pas comme une métadonnée.

Le fil rouge : **chaque projet est reproductible** — `main.py` (ou `Main.cs`) se déploie tel quel sur QuantConnect Cloud, et `research.ipynb` documente l'exploration qui a mené à la stratégie.

### Prochaines étapes

1. **Parcourir par niveau** : débutant (`CSharp-BTC-EMA-Cross`, `EMA-Cross-Stocks`, `AllWeather`) avant d'aborder les avancés (`Framework_Composite_TrendWeather`, `Portfolio-Optimization-ML`).
2. **Lire les contre-exemples** : ouvrir `PairsTrading/` et `ForexCarry/` pour comprendre *pourquoi* ils échouent — le diagnostic négatif est formateur.
3. **Consulter le détail** : `STRATEGIES_DETAIL.md` donne le contexte complet de chaque stratégie (catégorie, ML/DL/RL, clones QC Library).
4. **Reproduire sur QC Cloud** : créer un projet, copier le `main.py`, lancer le backtest, et comparer vos métriques au tableau ci-dessus.
5. **Étendre un projet Robuste** : choisir une stratégie *Robuste* (ex. `RegimeSwitching`, `SectorMomentum`) et itérer — changer l'univers, ajouter un filtre de risque, tester la sensibilité aux coûts de transaction.
6. **Voir les leçons transversales** : `docs/qc/quantconnect.md` recense les 20 patterns confirmés et les anti-patterns observés à travers ces 116 projets.

> **Rappel honnête** : un Sharpe de backtest, même *Robuste*, n'est pas une garantie live. Les coûts de transaction réels, le slippage et l'impact de marché dégradent systématiquement la performance paper. La barre *Robuste* (> 0.5 soutenu sur la période) est nécessaire mais pas suffisante — le walk-forward et l'out-of-sample strict restent obligatoires avant tout déploiement.

---

## Ressources

- [Descriptions détaillées](STRATEGIES_DETAIL.md) — Toutes les stratégies par catégorie
- [Leçons et patterns](../../../docs/qc/quantconnect.md) — 20 patterns confirmés + anti-patterns
- [Catalogue QC Cloud](../docs/qc_strategies_catalog.md) — Métriques par stratégie avec Cloud IDs
- [Quick Tour](../QUICK_TOUR.md) — Vue d'ensemble en 2 minutes
- [QuantConnect Lab](https://www.quantconnect.com/terminal) · [Documentation](https://www.quantconnect.com/docs) · [Forum](https://www.quantconnect.com/forum)

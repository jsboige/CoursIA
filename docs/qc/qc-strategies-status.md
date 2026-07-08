# Statut des stratégies QuantConnect — source de vérité

> **Issue parente** : [#1621 EPIC Consolidation QC/Trading](https://github.com/jsboige/CoursIA/issues/1621) (mandat user 2026-05-27).
> **Partition** : `po-2024:CoursIA` (QC). **Tranche 1** (livrable incrémental — l'EPIC demande explicitement « un sujet par PR, ne pas tout faire d'un coup »).

Ce document est le **point d'entrée unique** pour un visiteur qui découvre les 111 stratégies sous `MyIA.AI.Notebooks/QuantConnect/projects/` (112 entrées brutes, dont `_docs/` qui n'est pas une stratégie). Il cartographie les stratégies, leur type, leur source de données, et — là où l'évidence existe — leur statut (alive / superseded / needs-improvement / à confirmer).

## Méthodologie (honnête)

Les statuts ci-dessous sont **exclusivement dérivés d'évidence firsthand** :

- **Backtests documentés** dans la mémoire du cluster (baselines vérifiées cross-seed).
- **Figures de recherche** couvertes par la campagne EPIC [#5654](https://github.com/jsboige/CoursIA/issues/5654) (2026-07-08, 11 stratégies QC illustrées).

Les stratégies **sans backtest récent dédié** sont marquées **« À confirmer »** plutôt que de recevoir un statut fabriqué. Un backtest par stratégie (via QC Cloud, MCP `qc-mcp`) reste l'acceptance finale — voir [#1027](https://github.com/jsboige/CoursIA/issues/1027) pour la gate paper-trading/backtest.

## Les 4 types de notebooks (acceptance EPIC)

Le matériel QC mélange 4 types de notebooks qu'un visiteur doit distinguer :

| Type | Description | Localisation |
|------|-------------|--------------|
| **(a) Quantbook QC Cloud** | Notebook officiel utilisant `QuantBook()`, exécuté via QC Cloud (MCP `qc-mcp` / Playwright en fallback). Non exécutable localement. | `projects/*/research.ipynb`, `Python/QC-Py-*` |
| **(b) Research notebook lié** | Notebook de recherche compagnon d'un quantbook/stratégie `projects/`. | `projects/*/research_*.ipynb` |
| **(c) Standalone research** | Recherche indépendante, données locales (yfinance, pandas, sklearn). Aucun QC Cloud requis. | `research/research_*.ipynb` (18 notebooks) |
| **(d) Placeholder pédagogique** | Notebook de cours avec stubs `# TODO étudiant`. | `Python/QC-Py-*` (cours) |

**Note** : `projects/Research-Executor/` est un **harness d'exécution** (`main.py` + `runner.ipynb` + MockQB), pas une stratégie ni une zone de recherche — README explicite : « Type: Utility (research execution harness, not a trading strategy) ».

## Stratégies vérifiées (statut firsthand)

| Stratégie | Type | Classe d'actifs | Statut | Évidence |
|-----------|------|-----------------|--------|----------|
| `LongShortHarvest-QC` | Composite pairs | Multi-actifs | **Alive — BEATS** | Baseline cluster 98.7% (backtest vérifié) ; figure #5740 |
| `Framework_Composite_FamaFrenchAllWeather` | Composite | Multi-actifs | **Alive — BEATS** | 87.5% OOS (backtest vérifié) |
| `DynamicVIXSpyRegime-QC` | Régime VIX | US Equity | **Alive** | 69.4% (backtest vérifié) |
| `AllWeather` | Multi-asset risk-parity | Actions/Bonds/Or/Commodities | **Alive** | Figure #5743 |
| `EMA-Cross-Index` | Trend EMA | US Equity (SPY) | **Alive** | Figure #5746 |
| `EMA-Cross-Crypto` | Trend EMA | Crypto (BTC) | **Alive** | Figure #5750 |
| `ML-RandomForest` | ML supervisé (RF) | US large-cap | **Alive** | Figure #5747 |
| `ML-XGBoost` | ML supervisé (XGBoost) | US large-cap | **Alive** | Figure #5749 |
| `ForexCarry` | FX carry/momentum | G10 FX | **Alive** | Figure #5748 |
| `RiskParity` / `Cloud-RiskParity-Composite` | Inverse-vol risk-parity | Multi-actifs | **Needs-improvement** (plafond structurel) | Sharpe 0.399 (contre-exemple pédagogique) ; figure #5753 |
| `DualMomentum` | Momentum dual-asset | Multi-actifs | **Superseded** | Échec TLT 2022 → remplacé par `DualMomentumNoTLT` |
| `DualMomentumNoTLT` | Momentum (sans TLT) | Multi-actifs | **Alive** (remplacement) | Figure #5754 |

## Régimes de performance (connaissance cluster firsthand)

Backtests cross-stratégies 2022–2024 (stress test) — un visiteur peut anticiper le comportement d'une stratégie selon sa classe :

| Régime | Comportement typique |
|--------|----------------------|
| Value / Factor / Trend classique | **Effondrement** (−62% à −85%) |
| Structured ML / Composites | **Tien** (−2% à −14%) |
| High-Turnover US Equity | **Near-immune** (0% à −2%) |
| Low-Turnover Multi-Asset / Crypto | **Vulnérable** (−30% à −43%) |

## Inventaire à compléter (tranches suivantes)

Les stratégies ci-dessus sont la **tranche 1 vérifiée**. Les ~100 stratégies restantes sont listées ci-dessous par catégorie (dénombrement fiable via `git ls-tree`) ; leur statut individuel reste **à confirmer par un backtest dédié** (scope séparé, gated QC Cloud).

| Catégorie | Dénombrement | Exemples |
|-----------|--------------|----------|
| `ML-*` (ML supervisé / DL) | 19 | `ML-Classification`, `ML-DeepLearning`, `ML-SVM`, `ML-FinBERT-Sentiment`, `ML-Temporal-CNN`, `ML-HeadShoulders-CNN`, `ML-LLM-Summarization` |
| `CSharp-*` (algorithmes C# de référence) | 3 | `CSharp-BTC-EMA-Cross`, `CSharp-BTC-MACD-ADX`, `CSharp-CTG-Momentum` |
| `Cloud-*` (composites QC Cloud) | 4 | `Cloud-MeanReversion-Sectors`, `Cloud-RiskParity-Composite`, `Cloud-SectorRotation-Momentum`, `Cloud-VolTargeting` |
| `Vol-*` (ex-ESGF, dégénéricisées) | 2 | Stratégies renommées post-cours ESGF (mandat #1621) |
| RL (RL/PPO/DQN) | 4 | `RL-DQN-Trading`, `RL-Options-Hedging`, `RL-Portfolio`, `Reinforcement-Learning-Trading` |
| DL (LSTM/Transformer/Mamba/TFT) | 9 | `DL-LSTM`, `LSTM-Forecasting`, `Crypto-LSTM-Prediction`, `Chronos-Foundation-Forecasting`, `Mamba-Crypto-Ranking`, `TFT-Crypto-Ranking`, `Ensemble-DLinear-TFT` |
| Options | 5 | `Option-Wheel`, `Dynamic-Options-Wheel`, `Options-VGT`, `OptionsIncome`, `RL-Options-Hedging` |
| Trend / Momentum | 12 | `Trend-Following`, `MomentumStrategy`, `SectorMomentum`, `LeveragedETFMomentum-QC`, `Multi-Layer-EMA`, `VolTarget-Momentum` |
| Mean Reversion / Pairs / StatArb | 7 | `MeanReversion`, `PairsTrading`, `ETF-Pairs`, `PCA-StatArbitrage`, `TrendFilteredMeanReversion` |
| Composites (`Framework_Composite_*` / `composite-*`) | 7 | `Framework_Composite_EMATrend`, `Framework_Composite_MomentumRegime`, `Framework_Composite_TrendWeather`, `composite-c1-multiasset`, `composite-c2-equityfactor` |
| Vol / Régime / Risk | 8 | `Vol-GARCH-Target`, `VIX-TermStructure`, `RegimeSwitching`, `Markov-Regime-Detection`, `Adaptive-Conformal-Risk`, `InverseVolatility-Rank` |
| Autres | variable | `BTC-ML`, `GraphSAGE-MultiAsset-Ranking`, `HAR-RV-J-Kelly`, `PuppiesOfTheDow-QC`, `TermStructureCommodities-QC`, `TurnOfMonth`, `TradingCosts-Optimization`, … |

**Liste exhaustive** : `git ls-tree -d --name-only origin/main MyIA.AI.Notebooks/QuantConnect/projects/` (112 entrées brutes, dont `_docs/` — soit **111 stratégies** ; `Research-Executor` est un harness d'exécution, pas une stratégie, cf. note ci-dessus).

## Travaux connexes

- **Checkpoints ML** : `ML-Training-Pipeline/` (444 MB `.pt`, 137 modèles) — migration Git LFS + purge des obsolètes = gated user (mandat 2026-05-27). Non livré.
- **Papertrading** : `Python/QC-Py-40-PaperTrading-Binance.ipynb`, `Python/QC-Py-41-PaperTrading-IBKR.ipynb` — statut à confirmer (gate [#1027](https://github.com/jsboige/CoursIA/issues/1027)).
- **Notebooks cours** : `Python/QC-Py-01..35` + `Cloud-01..07` + companion `Python/research/` (QC-Py-19/22) — cohérents, audit prod-ready à part.

## Voir aussi

- [docs/qc/quantconnect.md](quantconnect.md) — structure complète QC, MCP Docker, livre de référence
- [docs/qc/qc-comparative-backtests.md](qc-comparative-backtests.md) — backtests comparatifs
- [#1621](https://github.com/jsboige/CoursIA/issues/1621) — EPIC Consolidation QC/Trading
- [#5654](https://github.com/jsboige/CoursIA/issues/5654) — EPIC Illustration READMEs (figures)
- [#1027](https://github.com/jsboige/CoursIA/issues/1027) — paper-trading / backtest gate
